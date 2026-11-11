-- Prove2me | Theorems.Thm_NecklacePPAD_Main_lemma_4_7
-- name    : NecklacePPAD.Main.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:10:16.769117+00:00
-- url     : https://prove2.me/theorems/8701c5a8-c8a2-4d23-91e6-14e6aeb22995
-- title:
--   Lemma 4.7 (gate correctness) — NOR, NP and NOT colours compute their gates under val
-- statement:
--   Under the standing assumptions of §4.2 and for any split $\ell$ of the constructed necklace (normalised to $\ell(1)=0$): (1) for the NOR colour of a gate $(\mathrm{NOR},u,v,w)$: if $\mathrm{val}(u)=1$ or $\mathrm{val}(v)=1$ then $\mathrm{val}(w)=0$, and if $\mathrm{val}(u)=\mathrm{val}(v)=0$ then $\mathrm{val}(w)=1$; (2) for the NP colour of a gate $(\mathrm{PURIFY},u,v,w)$, with input $u$ and outputs $v',w'$: if $\mathrm{val}(u)\in\{0,1\}$ then $\mathrm{val}(v')=\mathrm{val}(w')=1-\mathrm{val}(u)$, and in every case at least one of $\mathrm{val}(v'),\mathrm{val}(w')$ lies in $\{0,1\}$; (3) for a NOT colour with input list $(y,y)$ and output $z$: if $\mathrm{val}(y)\in\{0,1\}$ then $\mathrm{val}(z)=1-\mathrm{val}(y)$.
--
--   Differences from the source:
--   - reading: standing assumptions of §4.2: half-sizes b_NOR ≥ 5, b_NP ≥ 4, b_NOT ≥ 3 fixed, (V, G) a Pure-Circuit instance → hypotheses 5 ≤ H.bNOR, 4 ≤ H.bNP, 3 ≤ H.bNOT and I.WellFormed; reason: the section fixes them once at its top; Definition 3.2 requires distinct gate nodes and one gate per output
--   - encoding: colour order d_1, …, d_n "arbitrarily" and the beads of Σ^c_i "in any order" → an arbitrary Layout (a permutation of the colours and, for every c and i, any permutation of the canonical Σ^c_i); reason: every choice of the page is a Layout and conversely
--   - encoding: auxiliary nodes v′, w′ of a PURIFY gate; V⁺ → V⁺ = Fin n ⊕ (gate index × Bool), v′ = inr (k, false), w′ = inr (k, true); auxiliary slots of NOR gates are hosted by no colour; reason: a node type for V⁺; unused slots are never read
--   - encoding: ℓ any split, complemented if necessary so that ℓ(1) = 0; val(x) = R_{h(x)}(σ(x)) → Layout.normLab complements ℓ when lab ℓ 0 = true; Layout.val reads R with that labelling; reason: the page’s normalisation, made explicit
--   - encoding: "let d be the NOR colour of (NOR, u, v, w)" / "the NP colour with input u and outputs v′, w′" → quantified over the gates: the k-th gate is nor u v w / purify u v w, with v′ = inr (k, false), w′ = inr (k, true); reason: each such gate has exactly that colour
--   - encoding: 1 − val(·) on {0, 1} → PVal.neg; reason: same values on {0, 1}
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Lemma 4.7, p. 7 (PDF 9)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Construction

set_option autoImplicit false

namespace NecklacePPAD.Main

open LpBallVI.Affine

/-- **Lemma 4.7 (gate correctness)** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission,
sha256 d5b5449c…, p. 7 (PDF 9)). With half-sizes `b_NOR ≥ 5`, `b_NP ≥ 4`, `b_NOT ≥ 3`, a
Pure-Circuit instance, any choice of orders and any split `ℓ` of the constructed necklace:
(1) for the NOR colour of `(NOR, u, v, w)`: `val(u) = 1` or `val(v) = 1` gives `val(w) = 0`, and
`val(u) = val(v) = 0` gives `val(w) = 1`;
(2) for the NP colour of `(PURIFY, u, v, w)` with outputs `v′, w′`: `val(u) ∈ {0, 1}` gives
`val(v′) = val(w′) = 1 − val(u)`, and in every case one of `val(v′), val(w′)` lies in `{0, 1}`;
(3) for a NOT colour with input list `(y, y)` and output `z`: `val(y) ∈ {0, 1}` gives
`val(z) = 1 − val(y)`. -/
theorem lemma_4_7 (H : HalfSizes) (hNOR : 5 ≤ H.bNOR) (hNP : 4 ≤ H.bNP) (hNOT : 3 ≤ H.bNOT)
    (I : PCInst) (hI : I.WellFormed) (L : Layout I H) (ℓ : Fin L.necklace.N → Bool)
    (hℓ : L.necklace.IsSplit ℓ) :
    (∀ (k : Fin I.gates.length) (u v w : Fin I.n), I.gates.get k = .nor u v w →
      ((L.val ℓ (.inl u) = .one ∨ L.val ℓ (.inl v) = .one) → L.val ℓ (.inl w) = .zero) ∧
      (L.val ℓ (.inl u) = .zero ∧ L.val ℓ (.inl v) = .zero → L.val ℓ (.inl w) = .one)) ∧
    (∀ (k : Fin I.gates.length) (u v w : Fin I.n), I.gates.get k = .purify u v w →
      (L.val ℓ (.inl u) ≠ .bot →
        L.val ℓ (.inr (k, false)) = PVal.neg (L.val ℓ (.inl u)) ∧
        L.val ℓ (.inr (k, true)) = PVal.neg (L.val ℓ (.inl u))) ∧
      (L.val ℓ (.inr (k, false)) ≠ .bot ∨ L.val ℓ (.inr (k, true)) ≠ .bot)) ∧
    (∀ d : Fin (numColours I), (gad I d).kind = .not → ∀ (y z : Node I) (κ : ℕ),
      (gad I d).inputs = [y, y] → (z, κ) ∈ (gad I d).outputs →
      L.val ℓ y ≠ .bot → L.val ℓ z = PVal.neg (L.val ℓ y)) := by sorry

end NecklacePPAD.Main
