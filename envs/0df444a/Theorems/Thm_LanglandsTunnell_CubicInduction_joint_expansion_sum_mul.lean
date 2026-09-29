-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_sum_mul
-- name    : LanglandsTunnell.CubicInduction.joint_expansion_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b231f070-8ddf-55d0-bbb0-0a2691c445ed
-- title:
--   Joint Whittaker expansions are linear in the form
-- statement:
--   Fix real numbers $\rho$ and $\delta$, natural numbers $n$, $J$, $m$, a family of complex exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$, continuous functions $v_1,\dots,v_m : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$, coefficient functions $c^{(l)}_{ij} : \mathbb{R} \times \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ and second coefficients $c'^{(l)}_{iji'j'} : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$. Throughout, the Whittaker function of $\Phi$ is $W(\Phi)(g) = \int\!\!\int\!\!\int \Phi(u(x,y,z)\,g)\,\psi_{\mathbb{Q}}(-(x+y))$, the triple integral being taken against the Haar measure of $\mathbb{A}_{\mathbb{Q}}$ conditioned on the adelic box (the product of a fundamental domain for the lattice at the infinite places with the integral finite adeles), $u(x,y,z)$ the upper unipotent matrix with entries $x$, $z$, $y$ in positions $(1,2)$, $(1,3)$, $(2,3)$, and $\psi_{\mathbb{Q}}$ the standard additive character; and $\mathrm{diag}(y_1y_2, y_2, 1)$ denotes the image in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ of that real diagonal matrix under the archimedean inclusion (the unit it defines when invertible, and $1$ otherwise). The hypothesis is that each $v_l$ carries a joint expansion in this sense: (i) each $(y,k) \mapsto c^{(l)}_{ij}(y,k)$ is continuous on $\{y > 0\}$; (ii) for every compact $K$ and every $b \ge 1$ there is $C$ with $\bigl\| W(v_l)(\mathrm{diag}(y_1y_2,y_2,1)\,k) - \sum_{i,j} c^{(l)}_{ij}(y_2,k)\, y_1^{e_i} (\log y_1)^j \bigr\| \le C\, y_1^{\rho+\delta}$ for all $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$; (iii) each $c'^{(l)}_{iji'j'}$ is continuous; (iv) for every compact $K$ there is $C$ with $\bigl\| c^{(l)}_{ij}(y_2,k) - \sum_{i',j'} c'^{(l)}_{iji'j'}(k)\, y_2^{e_{i'}} (\log y_2)^{j'} \bigr\| \le C\, y_2^{\rho+\delta}$ for all $k \in K$, all $i,j$ and $0 < y_2 \le 1$. The conclusion is that for any scalars $a_1,\dots,a_m \in \mathbb{C}$ the four clauses (i)–(iv) hold, with the same $\rho$, $\delta$, $e$, $n$ and $J$, for the function $g \mapsto \sum_l a_l v_l(g)$ with coefficients $\sum_l a_l c^{(l)}_{ij}$ and $\sum_l a_l c'^{(l)}_{iji'j'}$.
--
--   This records that the property of possessing a joint exponent–logarithm expansion of the Whittaker function along the archimedean torus, together with its two layers of coefficients, is stable under complex linear combinations, the coefficients transforming linearly. It is used in the construction of the double-slot leading-coefficient data, namely by [`LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule`](thm.html#LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule) and [`LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top`](thm.html#LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top), where the coefficient assignments must be seen as linear maps on a space of automorphic functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_joint_expansion_sum_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.joint_expansion_sum_mul
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (m : ℕ) (v : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : ∀ l, Continuous (v l))
    (cv : Fin m → Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv' : Fin m → Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ l : Fin m,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (cv l) i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (v l)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, (cv l) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous ((cv' l) i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖(cv l) i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, (cv' l) i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (a : Fin m → ℂ) :
    (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (fun i j y k => ∑ l : Fin m, a l * cv l i j y k) i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun g => ∑ l : Fin m, a l * v l g)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, (fun i j y k => ∑ l : Fin m, a l * cv l i j y k) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous ((fun i j i' j' k => ∑ l : Fin m, a l * cv' l i j i' j' k) i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖(fun i j y k => ∑ l : Fin m, a l * cv l i j y k) i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, (fun i j i' j' k => ∑ l : Fin m, a l * cv' l i j i' j' k) i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)) := by sorry
