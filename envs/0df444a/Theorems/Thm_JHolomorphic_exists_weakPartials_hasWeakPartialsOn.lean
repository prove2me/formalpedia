-- Prove2me | Theorems.Thm_JHolomorphic_exists_weakPartials_hasWeakPartialsOn
-- name    : JHolomorphic.exists_weakPartials_hasWeakPartialsOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:48:57.541504+00:00
-- url     : https://prove2.me/theorems/7cde76b5-56de-4c52-92fc-cf430221d9fd
-- title:
--   A $W^{1,p}_{\mathrm{loc}}$ solution of the nonlinear Cauchy–Riemann equation lies in $W^{2,p}_{\mathrm{loc}}$
-- statement:
--   Let $p>2$, let $E$ be a finite-dimensional real normed space and let $J$ be a smooth almost complex structure on an open set $O\subseteq E$. Let $U\subseteq\mathbb{C}$ be open and let $u:U\to O$ be continuous, with $u\in W^{1,p}_{\mathrm{loc}}(U)$ and $\partial_su+J(u)\,\partial_tu=0$ almost everywhere on $U$ for its weak partial derivatives. Then $u\in W^{2,p}_{\mathrm{loc}}(U)$: $u$ has weak partial derivatives $u_s,u_t$ on $U$, the maps $u_s$ and $u_t$ have weak partial derivatives $u_{ss},u_{st}$ and $u_{ts},u_{tt}$ on $U$, and all six maps lie in $L^p(K)$ for every compact $K\subseteq U$.
--
--   This is the first step of interior elliptic regularity for pseudoholomorphic maps (Wendl, Theorem 2.22 (1)).
--
--   **Formalization Note** The hypothesis is `IsWeakJHolomorphicOn p J O U u`. Weak partial derivatives are in the sense of `HasWeakPartialsOn` (testing against real $C^\infty$ functions with compact support in $U$), and $L^p(K)$ is `MemLp · (ENNReal.ofReal p) (volume.restrict K)`. The six maps are asserted to exist; they are not required to coincide with the weak partials supplied by the hypothesis (weak partials are unique almost everywhere anyway).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, §2.5 (regularity of $J$-holomorphic maps)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

/-- Let `p > 2` and let `J` be a smooth almost complex structure on an open set `O ⊆ E`. A
`W^{1,p}_loc` solution `u` of `∂ₛu + J(u) ∂ₜu = 0` on an open set `U ⊆ ℂ` lies in
`W^{2,p}_loc(U)`: it has weak partial derivatives `uₛ`, `uₜ` on `U` which themselves have weak
partial derivatives on `U`, and all of these lie in `L^p(K)` for every compact `K ⊆ U`. -/
theorem exists_weakPartials_hasWeakPartialsOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    ∃ us ut uss ust uts utt : ℂ → E, HasWeakPartialsOn U u us ut ∧
      HasWeakPartialsOn U us uss ust ∧ HasWeakPartialsOn U ut uts utt ∧
      ∀ K ⊆ U, IsCompact K →
        MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp uss (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ust (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp uts (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp utt (ENNReal.ofReal p) (volume.restrict K) := by
  sorry

end JHolomorphic
