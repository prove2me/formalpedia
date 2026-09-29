-- Prove2me | Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
-- name    : NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/a9cfed3b-783d-50fa-a008-1299dfef06aa
-- title:
--   Rescaled T-unit lattice with divisibility condition
-- statement:
--   Let $K$ be a number field, $T$ a finite set of nonzero prime ideals of $\mathcal O_K$, and $f$ an assignment of a natural number to every such prime, with $f v>0$ for every $v\in T$. Write $r$ for the number of infinite places of $K$, index the infinite places by $\mathrm{Fin}\,r$ and the elements of $T$ by $\mathrm{Fin}\,|T|$ via the chosen enumerating equivalences. The assertion is the existence of an additive subgroup $\Lambda$ of $(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,|T|\to\mathbb Z)$ and a map $\mathrm{Log}:K^\times\to(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,|T|\to\mathbb Z)$ such that: $\mathrm{Log}(u)$ is given by the logarithmic embedding, its $i$-th real coordinate being $m_w\log|u|_w$ for the $i$-th infinite place $w$ (with $m_w$ its multiplicity) and its $j$-th integral coordinate being the additive value of the normalised valuation at the $j$-th prime of $T$; $\mathrm{Log}(uu')=\mathrm{Log}(u)+\mathrm{Log}(u')$; a pair $\gamma=(x,k)$ lies in $\Lambda$ exactly when some $u\in K^\times$ has valuation $1$ at every prime outside $T$ and satisfies $\mathrm{Log}(u)=(x,(f_{v_j}k_j)_j)$; $\Lambda$ carries the discrete topology; every $\gamma\in\Lambda$ satisfies $\sum_i x_i=\sum_j\bigl(-\log N(v_j)^{f_{v_j}}\bigr)k_j$, where $N$ denotes the absolute ideal norm; and, if $T$ is nonempty, the vector $j\mapsto-\log N(v_j)^{f_{v_j}}$ is not the zero vector.
--
--   This is the $S$-unit (Dirichlet) lattice of $K$ relative to the finite set $T$, in the variant in which the prescribed valuations at the primes of $T$ are required to be divisible by given positive integers $f_v$, together with the product formula read off on it. It supplies the lattice and weight vector for the winding data used in the construction of hyperbolic class sums and twisted orbital integrals for $\mathrm{GL}_2$ over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v) :
    ∃ (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
      (Log : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      (∀ u : Kˣ, Log u =
        (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
          fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u))) ∧
      (∀ u u' : Kˣ, Log (u * u') = Log u + Log u') ∧
      (∀ γ, γ ∈ Λ ↔ ∃ u : Kˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧
          Log u = (γ.1, fun j => (f (T.equivFin.symm j).1 : ℤ) * γ.2 j)) ∧
      DiscreteTopology Λ ∧
      (∀ γ ∈ Λ, ∑ i, γ.1 i =
        ∑ j, -Real.log ((Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) ^ f (T.equivFin.symm j).1) * (γ.2 j : ℝ)) ∧
      (T.Nonempty → (fun j : Fin T.card =>
        -Real.log ((Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) ^ f (T.equivFin.symm j).1)) ≠ 0) := by sorry
