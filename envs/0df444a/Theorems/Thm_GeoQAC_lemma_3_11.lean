-- Prove2me | Theorems.Thm_GeoQAC_lemma_3_11
-- name    : GeoQAC.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:09.153095+00:00
-- url     : https://prove2.me/theorems/e345c241-0086-48a0-aac7-3b79169fdda5
-- title:
--   Lemma 3.11 — grouping by column overlap
-- statement:
--   Let $H_1,\dots,H_m$ be nonzero Hermitian operators supported on nonempty connected regions $D_1,\dots,D_m\subseteq\Lambda=[w]\times[h]$. If each column index belongs to at most $r$ of the column projections $I(D_i)$, then every pure state $|\psi\rangle$ satisfies
--   $$
--   \mathrm{Var}_\psi\Big(\sum_i H_i\Big)\le r\cdot\Gamma(\psi)\cdot\sum_i\|H_i\|^2 .
--   $$
--   Here $\|\cdot\|$ is the operator norm.
--
--   The lemma converts a sum of local observables with bounded column overlap into a bound in terms of $\Gamma$; it combines the error terms in the proof of Lemma 3.9.
--
--   Differences from the source: none.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 3.11, p.18

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_GeoQAC_lmv

namespace GeoQAC

open DHRUniq (IsUnitVec)

open ObliviousRSP (pureState)

open scoped Matrix.Norms.L2Operator

/-- **Lemma 3.11** (arXiv:2604.07178, version of 2026-11-03, p.18). Let `H_1, …, H_m` be nonzero
Hermitian operators supported on nonempty connected regions `D_1, …, D_m ⊆ Λ = [w] × [h]`. If each
column index belongs to at most `r` of the intervals `I(D_i)`, then every pure state `|ψ⟩` satisfies
`Var_ψ(∑_i H_i) ≤ r · Γ(ψ) · ∑_i ‖H_i‖²`.

**Formalization Note.** `‖·‖` is the L2 operator norm; `ψ` is a unit vector and `Γ(ψ)` is
`lmv (pureState ψ)`. -/
theorem lemma_3_11 {w h m r : ℕ} (H : Fin m → Matrix (Pos w h → Bool) (Pos w h → Bool) ℂ)
    (D : Fin m → Finset (Pos w h))
    (hH : ∀ i, (H i).IsHermitian ∧ H i ≠ 0 ∧ IsSupportedOn (D i) (H i))
    (hD : ∀ i, IsConnectedRegion (D i))
    (hr : ∀ c : Fin h, (Finset.univ.filter fun i => c ∈ colProj (D i)).card ≤ r)
    (ψ : (Pos w h → Bool) → ℂ) (hψ : IsUnitVec ψ) :
    var (pureState ψ) (∑ i, H i) ≤ (r : ℝ) * lmv (pureState ψ) * ∑ i, ‖H i‖ ^ 2 := by sorry

end GeoQAC
