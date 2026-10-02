-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_integration_by_parts
-- name    : HunterPDE.Parabolic.integration_by_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:19:53.795472+00:00
-- url     : https://prove2.me/theorems/c0ca6c9f-2a4b-4878-9bd5-780304f040ca
-- title:
--   Theorem 6.42 — integration by parts in time for a Hilbert triple
-- statement:
--   Let $\mathcal{V} \hookrightarrow \mathcal{H} \hookrightarrow \mathcal{V}'$ be a Hilbert triple and $T > 0$. Suppose that $u, v \in L^2(0,T;\mathcal{V})$ and their weak time derivatives satisfy $u_t, v_t \in L^2(0,T;\mathcal{V}')$. Then
--   $$\int_0^T \langle u_t, v\rangle\,dt = (u(T), v(T))_{\mathcal{H}} - (u(0), v(0))_{\mathcal{H}} - \int_0^T \langle u, v_t\rangle\,dt,$$
--   where $u(0), u(T), v(0), v(T)$ are values of the continuous representatives $u, v \in C([0,T];\mathcal{H})$ given by Theorem 6.41.
--
--   The formula is used to identify the initial value of the Galerkin limit (Proposition 6.7).
--
--   **Formalization Note.** The continuous representatives are hypotheses `uc`, `vc`: any functions continuous on $[0,T]$ and equal to $u$, $v$ in $\mathcal{H}$ for a.e. $t \in (0,T)$ (Theorem 6.41 says they exist; they are unique on $[0,T]$). $\langle u, v_t\rangle$ is the pairing $v_t(t)(u(t))$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 209, Theorem 6.42

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_HilbertTriple

open MeasureTheory

namespace HunterPDE.Parabolic

/-- Theorem 6.42 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 209 (integration by parts in
time): let `𝒱 ↪ ℋ ↪ 𝒱'` be a Hilbert triple and `T > 0`. If `u, v ∈ L²(0, T; 𝒱)` and their weak
time derivatives (taken in `𝒱'`) satisfy `u_t, v_t ∈ L²(0, T; 𝒱')`, then
`∫₀ᵀ ⟨u_t, v⟩ dt = (u(T), v(T))_ℋ − (u(0), v(0))_ℋ − ∫₀ᵀ ⟨u, v_t⟩ dt`,
where `u(0), u(T), v(0), v(T)` are the values of the continuous representatives
`uc, vc ∈ C([0, T]; ℋ)` of Theorem 6.41 (any continuous functions on `[0, T]` equal to `u`, `v` a.e.
on `(0, T)`), and `⟨u, v_t⟩ = v_t(u)` is the `𝒱'`–`𝒱` duality pairing. -/
theorem integration_by_parts {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HT : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u v : ℝ → V) (ut vt : ℝ → StrongDual ℝ V)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo 0 T)))
    (hv : MemLp v 2 (volume.restrict (Set.Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Set.Ioo 0 T)))
    (hvt : MemLp vt 2 (volume.restrict (Set.Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (hdv : HasWeakTimeDeriv HT.toDualV T v vt)
    (uc vc : ℝ → H) (hucc : ContinuousOn uc (Set.Icc 0 T)) (hvcc : ContinuousOn vc (Set.Icc 0 T))
    (huc : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), uc t = HT.toH (u t))
    (hvc : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), vc t = HT.toH (v t)) :
    ∫ t in Set.Ioo 0 T, ut t (v t) =
      inner ℝ (uc T) (vc T) - inner ℝ (uc 0) (vc 0) - ∫ t in Set.Ioo 0 T, vt t (u t) := by sorry

end HunterPDE.Parabolic
