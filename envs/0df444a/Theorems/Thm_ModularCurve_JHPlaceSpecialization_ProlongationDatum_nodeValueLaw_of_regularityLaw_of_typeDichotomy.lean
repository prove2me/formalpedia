-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_nodeValueLaw_of_regularityLaw_of_typeDichotomy
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.nodeValueLaw_of_regularityLaw_of_typeDichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/53f58c4b-2271-5824-851b-94e196685382
-- title:
--   Node-value law from regularity law at supersingular nodes
-- statement:
--   Fix a prime $p$, a positive integer $M$ divisible by $p$ with $M/p$ positive, and a subgroup $H \le (\mathbb{Z}/M)^\times$; write $F_M$ for the function field $\mathrm{xHFunctionFieldBar}\,M\,H$ over $\overline{\mathbb{Q}}$, $F_{M/p}$ for the corresponding field at level $(M/p, \mathrm{infSubgroup}\,p\,M\,H)$, and let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$; let $\bar F$ be the $q$-expansion function field $\mathrm{Fbar}$ over $\kappa$ for the group $\Gamma_N = \mathrm{ΓN}\,p\,M\,H$. Given a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$, two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, a self-map $\delta$ of the places of $\bar F$ over $\kappa$, a finite set $SS$ of pairs of such places whose members are exactly the pairs $s$ with $s_2$ a supersingular place (in the sense of `ssPlacesQExp`) and $s_1 = \mathrm{Frob}(s_2)$, where $\mathrm{Frob} = \mathrm{qExpFrobeniusPlaceModL}$, a place-specialization packet `Psp` for $(p,M,H,A)$ and a prolongation datum `Rpd` consisting of regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, matched through $\theta$, assume: (i) the type dichotomy, i.e. for every place $W$ of $F_M$ either $\mathrm{reduceFst}_\alpha W = \mathrm{Frob}(\mathrm{reduceSnd}_{\beta,\delta} W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}_\alpha W)) = \mathrm{reduceSnd}_{\beta,\delta} W$, where $\mathrm{reduceFst}_\alpha W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{reduceSnd}_{\beta,\delta} W = \delta(\mathrm{sp}(W|_\beta))$; (ii) $\delta \circ \mathrm{Frob} = \mathrm{Frob} \circ \delta$; (iii) every supersingular place $y$ satisfies $\mathrm{Frob}(\delta(\mathrm{Frob}\,y)) = y$; (iv) the regularity law for $(\alpha,\beta,\delta,SS)$. Then the node-value law holds: for every $f \in F_M$ lying in the integers of both $R_1$ and $R_2$ with both residues non-zero, and every $s \in SS$ such that no place $V$ of $F_M$ with $\mathrm{ord}_V f \ne 0$ has $(\mathrm{reduceFst}_\alpha V, \mathrm{reduceSnd}_{\beta,\delta} V) = (s_1, s_2)$, there is a non-zero $c \in \kappa$ with $s_1$ taking the value $c$ at the $R_1$-residue of $f$ and $s_2$ taking the value $c$ at the $R_2$-residue of $f$.
--
--   This is the step which upgrades the regularity law at the supersingular gluing pairs to a statement that the two residues of a function take a common non-zero value at each node, the form needed when comparing divisor classes on the two components of the fibre of the modular curve at $p$. It feeds the construction of place specializations together with prolongation data and glued specializations used in the de Rham model of $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_nodeValueLaw_of_regularityLaw_of_typeDichotomy.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.nodeValueLaw_of_regularityLaw_of_typeDichotomy
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hcomm : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ v))
    (hss : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p, JHPlaceSpecialization.Fixed p M H hpM A δ y)
    (hreg : Rpd.RegularityLaw α β hα hβ δ SS) :
    Rpd.NodeValueLaw α β hα hβ δ SS := by sorry
