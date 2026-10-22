-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_prodMk
-- name    : JHolomorphic.HasWeakPartialsOn.prodMk
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:43:06.173344+00:00
-- url     : https://prove2.me/theorems/63c58d1d-8dec-4fae-9e6b-55c57722994a
-- title:
--   Weak partial derivatives of a pair of maps
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open. If $u_s,u_t$ are weak partial derivatives of $u:\mathbb{C}\to E$ on $U$ and $v_s,v_t$ are weak partial derivatives of $v:\mathbb{C}\to F$ on $U$, all six maps being integrable on every compact subset of $U$, then $(u_s,v_s)$ and $(u_t,v_t)$ are weak partial derivatives of $z\mapsto(u(z),v(z))$ on $U$.
--
--   **Formalization Note** $E,F$ are finite-dimensional real normed spaces and $E\times F$ carries the product norm. Weak partial derivatives are in the sense of `HasWeakPartialsOn` (testing against real $C^\infty$ functions with compact support in $U$, Bochner integrals over $\mathbb{C}$), and "almost every $z\in U$" is `∀ᵐ z ∂(volume.restrict U)`.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak partial derivatives of a pair are the pairs of weak partial derivatives. -/
theorem HasWeakPartialsOn.prodMk {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set ℂ} {u us ut : ℂ → E} {v vs vt : ℂ → F}
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U v vs vt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K ∧
        IntegrableOn v K ∧ IntegrableOn vs K ∧ IntegrableOn vt K) :
    HasWeakPartialsOn U (fun z => (u z, v z)) (fun z => (us z, vs z)) (fun z => (ut z, vt z)) := by
  sorry

end JHolomorphic
