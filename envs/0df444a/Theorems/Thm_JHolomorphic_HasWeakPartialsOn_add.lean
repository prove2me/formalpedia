-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_add
-- name    : JHolomorphic.HasWeakPartialsOn.add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:30:31.978127+00:00
-- url     : https://prove2.me/theorems/cadeaad6-1aec-4793-8d51-77a4bed1fc6b
-- title:
--   Weak partial derivatives are additive
-- statement:
--   Let $U\subset\mathbb{C}$ and let $E$ be a real normed space. Suppose $u,v:\mathbb{C}\to E$ have weak partial derivatives $u_s,u_t$ and $v_s,v_t$ on $U$ (tested against real $C^\infty$ functions with compact support in $U$), and that $u,u_s,u_t,v,v_s,v_t$ are integrable on every compact $K\subset U$. Then $u+v$ has weak partial derivatives $u_s+v_s$ and $u_t+v_t$ on $U$.
--
--   This is the additivity of weak derivatives, used whenever a $W^{1,p}_{\mathrm{loc}}$ map is assembled from several pieces.
--
--   **Formalization Note** Weak partials are `JHolomorphic.HasWeakPartialsOn U u us ut` from the imported setting; local integrability is `IntegrableOn _ K` for every compact `K ⊆ U`. No openness of $U$ is required.
-- source:
--   Standard; Used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Weak partial derivatives of a sum: if `u` and `v` have weak partials on `U` and `u, uₛ, uₜ, v, vₛ, vₜ`
are integrable on every compact subset of `U`, then `u + v` has weak partials `uₛ + vₛ`, `uₜ + vₜ`. -/
theorem HasWeakPartialsOn.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {u us ut v vs vt : ℂ → E}
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U v vs vt)
    (hint1 : ∀ K ⊆ U, IsCompact K → IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K)
    (hint2 : ∀ K ⊆ U, IsCompact K → IntegrableOn v K ∧ IntegrableOn vs K ∧ IntegrableOn vt K) :
    HasWeakPartialsOn U (fun z => u z + v z) (fun z => us z + vs z) (fun z => ut z + vt z) := by
  sorry

end JHolomorphic
