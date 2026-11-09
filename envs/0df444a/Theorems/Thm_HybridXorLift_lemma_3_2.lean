-- Prove2me | Theorems.Thm_HybridXorLift_lemma_3_2
-- name    : HybridXorLift.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:39.469216+00:00
-- url     : https://prove2.me/theorems/e4b463cb-2dbc-4d83-8b5b-c46f153bb4de
-- title:
--   Lemma 3.2 — positivity, initial value $e^{-r|I|/(2q)}$ and parity correlation of $\Psi_{I,\zeta}$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   For every nonempty $I \subseteq [n]$, every $\zeta \in \{0,1\}^{\bar I}$ and every history $h$,
--   $$
--   \Psi_{I,\zeta}(h) \ge 0 \qquad\text{and}\qquad \Psi_{I,\zeta}(\varnothing) = e^{-r|I|/(2q)} , \tag{3.9}
--   $$
--   and
--   $$
--   \Big|\, \mathbb E_{z :\ z_{\bar I} = \zeta}\, (-1)^{\bigoplus_{i \in I} z_i}\, \ell_h(z) \Big| \le \Psi_{I,\zeta}(h). \tag{3.10}
--   $$
--
--   The potential is thus a valid measure of the correlation of the likelihood with the parity of the blocks in $I$, and it starts exponentially small in $r$.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 3.2, p.12 (PDF p.14)

import Definitions.Def_HybridXorLift_psi
import Definitions.Def_HybridXorLift_likelihood
import Definitions.Def_HybridXorLift_cubeAvg
import Definitions.Def_HybridXorLift_ParallelHybridAlg_histories
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 3.2 (Positivity, initial value, and parity correlation) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.12 (PDF p.14). For
nonempty `I ⊆ [n]`, `ζ ∈ {0,1}^Ī` and every history `h`: `Ψ_{I,ζ}(h) ≥ 0`,
`Ψ_{I,ζ}(∅) = e^{−r|I|/(2q)}` (3.9), and
`|E_{z : z_Ī = ζ} (−1)^{⊕_{i∈I} z_i} ℓ_h(z)| ≤ Ψ_{I,ζ}(h)` (3.10).

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. Histories are lists of recorded outcomes (`ParallelHybridAlg.histories`); partial assignments are full functions read only on their index set (`cubeAvg`). The sign `(−1)^{⊕_{i∈I} z_i}` is
`∏_{i∈I} (−1)^{z_i}`. -/
theorem lemma_3_2 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (I : Finset (Fin n)) (hI : I.Nonempty) (ζ : Fin n → Bool)
    (h : List (Step (Fin n × Fin r))) (hh : h ∈ A.histories) :
    0 ≤ psi A q I ζ h ∧
    psi A q I ζ [] = Real.exp (-((r : ℝ) * I.card / (2 * (q : ℝ)))) ∧
    |cubeAvg Iᶜ ζ (fun z => (∏ i ∈ I, if z i then (-1 : ℝ) else 1) * likelihood A h z)| ≤
      psi A q I ζ h := by sorry

end HybridXorLift
