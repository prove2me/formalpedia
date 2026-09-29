-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg
-- name    : ModularCurve.JHPlaceSpecialization.exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f3c0d4ba-0ca5-5519-a91f-06b00ba1db48
-- title:
--   Constant shift preserving a simple pole and both Gauss residues
-- statement:
--   Fix a prime $p$, a positive integer $M$ divisible by $p$ with $M/p$ positive, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H`, the $\overline{\mathbb{Q}}$-base change inside $\overline{\mathbb{Q}}((q))$ of the function field of $X_H(M)$, $F_{M/p}$ for the analogous field at level $M/p$ with the subgroup `infSubgroup p M H hpM`, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`. Given a $\overline{\mathbb{Q}}$-automorphism $\theta$ of $F_M$, integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, a self-map $\delta$ of the set of places of $\bar F/\kappa$, place-specialization data `Psp` (whose component `sp` carries places of $F_{M/p}$ to places of $\bar F$) and a prolongation datum `Rpd` for `Psp` and $\theta$ with regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, set $r_1(V) = \mathrm{sp}(V|_\alpha)$ and $r_2(V) = \delta(\mathrm{sp}(V|_\beta))$ for a place $V$ of $F_M/\overline{\mathbb{Q}}$. Let further $S$ be a finite set of elements of $\kappa$, $x_j \in F_M$, $B$ a finite set of places of $\bar F$, and $V_0$ a place of $F_M$ with $r_1(V_0), r_2(V_0) \in B$. Assume $g$ lies in the integers of both $R_1$ and $R_2$, that $\mathrm{ord}_{V_0} g = -1$ (where $\mathrm{ord}$ is the normalised discrete valuation attached to a place), and that every place $V \ne V_0$ with $\mathrm{ord}_V g < 0$ is good, i.e. there is $a \in A$ with $\mathrm{ord}_V(x_j - a) > 0$ and residue of $a$ outside $S$, and has $r_1(V) \notin B$, $r_2(V) \notin B$. The conclusion asserts the existence of $c \in A$, together with proofs that $g - c$ lies in the integers of $R_1$ and of $R_2$, such that: the residues satisfy $R_i.\mathrm{residue}(g - c) = R_i.\mathrm{residue}(g) - \bar c$ for $i = 1, 2$, where $\bar c$ is the image in $\bar F$ of the residue of $c$; both these residues are non-zero; $g - c \ne 0$; $\mathrm{ord}_{V_0}(g - c) = -1$; every pole of $g - c$ is a pole of $g$; every pole of $g$ is $V_0$ or good in the above sense; $r_1(V_0), r_2(V_0) \in B$; for each $t' \in B$ and each place $V'' \ne V_0$ of $F_M$ with $r_1(V'') = t'$, respectively $r_2(V'') = t'$, one has $\mathrm{ord}_{V''}(g - c) \ge 0$; for each $t' \in B$ neither $R_1.\mathrm{residue}(g) - \bar c$ nor $R_2.\mathrm{residue}(g) - \bar c$ has positive order at $t'$; and there is a finitely supported divisor $q$ on the places of $F_M/\overline{\mathbb{Q}}$ with $q(V) = \mathrm{ord}_V(g - c)$ for all $V$ and $\deg q = 0$.
--
--   This is the "section kit" step of the avoidance argument in the $\Gamma_H$-setting: a single element with a prescribed simple pole is shifted by a constant from $A$ so that its two Gauss residues remain non-zero and avoid the finite set $B$ of places of the fibre function field, while its pole set only improves. It is used by the two lemmas producing a principal degree-zero divisor with a simple pole at $V_0$ and otherwise good support, and cites the existence of principal divisors for `xHFunctionFieldBar`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

theorem ModularCurve.JHPlaceSpecialization.exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (S : Finset (ResidueField ↥A))
    (xj : ↥(xHFunctionFieldBar M H))

    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hB₁ : Psp.reduceFst α hα V₀ ∈ B) (hB₂ : Psp.reduceSnd β hβ δ V₀ ∈ B)
    (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers)
    (hgord : V₀.ord g = -1)
    (hfused : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → V.ord g < 0 →
      (∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
        Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B) :
    ∃ (c : ↥A)
      (h₁' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) ∈ Rpd.R₁.integers)
      (h₂' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) ∈ Rpd.R₂.integers),
      (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₁'⟩
        = Rpd.R₁.residue ⟨g, h₁⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) ∧
      (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₂'⟩
        = Rpd.R₂.residue ⟨g, h₂⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) ∧
      (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₁'⟩ ≠ 0) ∧
      (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₂'⟩ ≠ 0) ∧
      (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) ≠ 0) ∧
      (V₀.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ))) = -1) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ))) < 0 → V.ord g < 0) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord g < 0 → V = V₀ ∨
        ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
      Psp.reduceFst α hα V₀ ∈ B ∧ Psp.reduceSnd β hβ δ V₀ ∈ B ∧
      (∀ t', t' ∈ B → ∀ V'' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V'' ≠ V₀ → Psp.reduceFst α hα V'' = t' → 0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)))) ∧
      (∀ t', t' ∈ B → ∀ V'' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V'' ≠ V₀ → Psp.reduceSnd β hβ δ V'' = t' → 0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)))) ∧
      (∀ t', t' ∈ B → 0 < t'.ord (Rpd.R₁.residue ⟨g, h₁⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) → False) ∧
      (∀ t', t' ∈ B → 0 < t'.ord (Rpd.R₂.residue ⟨g, h₂⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) → False) ∧
      ∃ q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q V = V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)))) ∧ Divisor.degree q = 0 := by sorry
