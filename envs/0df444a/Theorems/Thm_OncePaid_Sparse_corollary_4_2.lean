-- Prove2me | Theorems.Thm_OncePaid_Sparse_corollary_4_2
-- name    : OncePaid.Sparse.corollary_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:48:55.180712+00:00
-- url     : https://prove2.me/theorems/880b4d8f-f429-4644-a4a5-5f0a5c9e5d4d
-- title:
--   Corollary 4.2 — on the LPS forced-run source, sound $(1+\lambda/400)$-approximation on $\{2,3,4\}^d$ with edge-path gain floor $\lambda$ needs $a(C)+1\ge(85/78)^n/(n+1)^2$
-- statement:
--   Let $\ell$ be a prime with $\ell\equiv305\pmod{404}$, let $i\in\mathbb F_\ell$ with $i^2=-1$, and put $n=\ell(\ell^2-1)/2$. Build the forced-run once-paid source $w$ from the LPS host $H_\ell=X_{101,\ell}$ for any order of its $2n$ vertices and any order inside each zero-run, with target $T=(01)^{2n}$ and resources the edges of $H_\ell$ together with the markers $z_1,\dots,z_n$ ($d=103n$ resources, source size $I=1+515n$). Fix $0<\lambda\le1$. Let $C$ be any min-plus circuit on the resource prices, with positive scalar gates and finite signed constants, such that
--
--   1. $C$ soundly $(1+\lambda/400)$-approximates $f_T$ on the full independent price domain: $f_T(c)\le C(c)\le(1+\lambda/400)\,f_T(c)$ for all $c\in\{2,3,4\}^d$;
--   2. every path from an edge-resource input to the output has gain at least $\lambda$ (paths from marker-resource inputs may have arbitrary positive gains).
--
--   Then
--
--   $$
--   a(C)+1\ \ge\ \frac{(85/78)^n}{(n+1)^2}.
--   $$
--
--   Since $I=1+515n$, the lower bound is exponential in the source size, while $f_T$ on the same family equals edge cover plus marker cost (Eq. (4.2)).
--
--   Differences from the source:
--   - encoding: "any fixed order" of the vertices and inside the runs → parameters $\sigma:\mathrm{Fin}(2n)\simeq V_L\sqcup V_R$ and `runs` with `ValidRuns`, every choice; the root $i$ → a parameter, every choice; markers → `Fin n`, 0-based; reason: Lean representation; the corollary holds for every choice.
--   - encoding: circuits → well-formed straight-line programs, $a(C)$ their addition-gate count, gain floor on the inputs in `Set.range Sum.inl` (edge resources); $f_T$ in `WithTop ℝ`; reason: Lean representation.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 21, Corollary 4.2 (PDF p. 23)

import Mathlib
import Definitions.Def_OncePaid_Sparse_OncePaid
import Definitions.Def_OncePaid_Sparse_Circuit
import Definitions.Def_OncePaid_Sparse_BipHost
import Definitions.Def_OncePaid_Sparse_ForcedRun
import Definitions.Def_OncePaid_Sparse_LPS

namespace OncePaid.Sparse

/-- Corollary 4.2 (Sparse subsequence fixed-error separation), p. 21. For every prime
`ℓ ≡ 305 (mod 404)`, every `i` with `i² = −1`, `n = ℓ(ℓ² − 1)/2`, every vertex order `σ` and
every valid within-run order of the forced-run source built from the LPS graph `H_ℓ`
(target `(01)^{2n}`, resources `E(H_ℓ) ⊕ {z_1, …, z_n}`), and every `0 < λ ≤ 1`: every
well-formed min-plus circuit with positive scalar gates and finite signed constants that is a
sound `(1 + λ/400)`-approximation of `f_T` on the full price domain `{2, 3, 4}^d`, with gain at
least `λ` on every path from an edge-resource input to the output (marker-resource paths
unconstrained), satisfies `a(C) + 1 ≥ (85/78)^n/(n + 1)²`. -/
theorem corollary_4_2 (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ % 404 = 305) (i : ZMod ℓ) (hi : i ^ 2 = -1)
    (σ : Fin (2 * lpsN ℓ) ≃ (lpsLeft ℓ ⊕ lpsRight ℓ))
    (runs : lpsLeft ℓ ⊕ lpsRight ℓ → List (Edge (lpsAdj ℓ i))) (hruns : ValidRuns runs)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (C : Circuit (Edge (lpsAdj ℓ i) ⊕ Fin (lpsN ℓ))) (hC : C.WF)
    (happrox : SoundApprox (1 + lam / 400)
      (onceOpt (forcedRunSource (lpsN ℓ) σ runs) (alternatingTarget (2 * lpsN ℓ))) C.eval
      (priceBox (Edge (lpsAdj ℓ i) ⊕ Fin (lpsN ℓ))))
    (hgain : C.GainFloorOn (Set.range Sum.inl) lam) :
    (85 / 78 : ℝ) ^ (lpsN ℓ) / ((lpsN ℓ : ℝ) + 1) ^ 2 ≤ (C.addCount : ℝ) + 1 := by sorry

end OncePaid.Sparse
