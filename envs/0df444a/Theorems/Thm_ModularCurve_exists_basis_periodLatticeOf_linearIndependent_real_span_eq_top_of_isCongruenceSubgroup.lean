-- Prove2me | Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
-- name    : ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/4f37bb8a-724b-50d4-83f8-98737beae34b
-- title:
--   The period lattice of a congruence subgroup is a full lattice
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ satisfying `CongruenceSubgroup.IsCongruenceSubgroup`, and consider the complex dual space $\operatorname{Hom}_{\mathbb C}(S_2(\Gamma),\mathbb C)$ of the space `CuspForm Γ 2` of weight-$2$ cusp forms for $\Gamma$. Inside it sits the $\mathbb Z$-submodule [`ModularCurve.periodLatticeOf Γ`](def/ModularCurve_PeriodOf.html#L65), by definition the $\mathbb Z$-span of the set of functionals [`ModularCurve.periodOf Γ γ`](def/ModularCurve_PeriodOf.html#L56), for $\gamma$ ranging over $\Gamma$, where [`ModularCurve.periodOf Γ γ`](def/ModularCurve_PeriodOf.html#L56) is `periodAlongOf Γ` applied to the pair of points $i$ and $\gamma \cdot i$ of the upper half plane, i.e. the functional sending a cusp form to its period from $i$ to $\gamma i$. The assertion is that there exist a natural number $n$ and a basis $b$ of this period lattice as a free $\mathbb Z$-module indexed by `Fin n` such that the $n$ elements $b_i$, viewed in $\operatorname{Hom}_{\mathbb C}(S_2(\Gamma),\mathbb C)$ regarded as a real vector space, are linearly independent over $\mathbb R$ and their $\mathbb R$-span is the whole of $\operatorname{Hom}_{\mathbb C}(S_2(\Gamma),\mathbb C)$. Thus the period lattice is a free $\mathbb Z$-module admitting a $\mathbb Z$-basis which is simultaneously an $\mathbb R$-basis of the ambient dual space; in particular $n = 2\dim_{\mathbb C} S_2(\Gamma)$, and the lattice is discrete and cocompact.
--
--   This is the real structure theorem behind the Eichler–Shimura isomorphism in the shape of the period lattice: integration of weight-$2$ cusp forms over the first homology of the compactified modular curve $X_\Gamma$ yields a full lattice in the dual of $S_2(\Gamma)$, so that the quotient is a complex torus. It underlies the construction of the Jacobian and its Tate modules as Hecke- and Galois-modules, and is cited in the treatment of Hecke operators on integral period groups and of the Galois representations attached to weight-$2$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.periodLatticeOf Γ)),
      LinearIndependent ℝ (fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) ∧
        Submodule.span ℝ (Set.range fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) = ⊤ := by sorry
