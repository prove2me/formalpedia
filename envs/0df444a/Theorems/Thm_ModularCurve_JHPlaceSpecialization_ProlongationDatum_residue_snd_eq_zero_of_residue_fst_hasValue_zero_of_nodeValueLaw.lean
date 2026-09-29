-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f5944970-121b-5cd2-8a98-993f1cfde236
-- title:
--   Second residue vanishes when the first vanishes at a node
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, $F_{M/p}$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\bar F$ for `Fbar p M H hpM` $\kappa$. Let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M$, let $\alpha,\beta : F_{M/p} \to F_M$ be $\overline{\mathbb{Q}}$-algebra maps with integral underlying ring maps, let $\delta$ be a self-map of the set of places of $\bar F$ over $\kappa$, and let $SS$ be a finite set of pairs of such places. Let `Psp` be a place specialisation datum for these data and `Rpd` a prolongation datum over `Psp` and $\theta$, consisting of two regular prolongations $R_1,R_2$ of $A$ to $F_M$ with residues in $\bar F$, such that $f$ is $R_2$-integral exactly when $\theta f$ is $R_1$-integral and the $R_2$-residue of $f$ equals the $R_1$-residue of $\theta f$. Assume the node-value law `NodeValueLaw` for $\alpha,\beta,\delta,SS$: for every $f$ integral for both prolongations with both residues nonzero, and every $s \in SS$ such that no place $V$ of $F_M$ with $\operatorname{ord}_V f \neq 0$ satisfies both $\mathrm{Psp}.sp(V|_\alpha) = s_1$ and $\delta(\mathrm{Psp}.sp(V|_\beta)) = s_2$, there is a nonzero $c \in \kappa$ at which the $R_1$-residue of $f$ has value $c$ at $s_1$ and the $R_2$-residue of $f$ has value $c$ at $s_2$. Let $u \in F_M$ be $R_1$-integral with nonzero $R_1$-residue, and let $s \in SS$ be such that no place $V$ of $F_M$ with $\operatorname{ord}_V u \neq 0$ reduces to $(s_1,s_2)$ under $(\mathrm{Psp}.sp(\,\cdot\,|_\alpha), \delta \circ \mathrm{Psp}.sp(\,\cdot\,|_\beta))$, and such that the $R_1$-residue of $u$ lies in the valuation subring of $s_1$ with residue there equal to the image of $0$. Then, whenever $u$ is also $R_2$-integral, its $R_2$-residue is $0$.
--
--   This is the step showing that a unit for the first prolongation whose first residue vanishes at a node of $SS$ cannot be a common unit for both prolongations: its second residue must vanish. It is used in the study of the two reductions of $X_H(M)$ at $p$, being cited by the results on units and divisors for a Deligne–Rapoport style model in [`ModularCurve.XHDRModelAtP`](def/ModularCurve_XHDRModelAtP.html#L81).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hnv : Rpd.NodeValueLaw α β hα hβ δ SS)
    (u : ↥(xHFunctionFieldBar M H)) (h₁ : u ∈ Rpd.R₁.integers) (hres₁ : Rpd.R₁.residue ⟨u, h₁⟩ ≠ 0)
    (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS)

    (hnodiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 → ¬ (Psp.reduceFst α hα V = s.1 ∧ Psp.reduceSnd β hβ δ V = s.2))
    (hvan : s.1.HasValue (Rpd.R₁.residue ⟨u, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) 0) :
    ∀ h₂ : u ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u, h₂⟩ = 0 := by sorry
