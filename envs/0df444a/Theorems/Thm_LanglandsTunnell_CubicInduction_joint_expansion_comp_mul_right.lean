-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right
-- name    : LanglandsTunnell.CubicInduction.joint_expansion_comp_mul_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8eab8b46-ec61-509d-b439-ef2bbb2e7c1a
-- title:
--   Right translation acts on joint Whittaker expansions on GL₃
-- statement:
--   Fix reals $\rho,\delta$, naturals $n,J$, exponents $e : \mathrm{Fin}\,n \to \mathbb C$, a function $v$ on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$, coefficient functions $cv_{ij} : \mathbb R \times \mathrm{GL}_3(\mathbb A_{\mathbb Q}) \to \mathbb C$ and second coefficients $cv'_{iji'j'} : \mathrm{GL}_3(\mathbb A_{\mathbb Q}) \to \mathbb C$ ($i,i' \in \mathrm{Fin}\,n$, $j,j' \in \mathrm{Fin}\,J$). The hypothesis is the four-clause joint-expansion block for $v$: (i) each $(y,k) \mapsto cv_{ij}(y,k)$ is continuous on $\{y > 0\}$; (ii) for every compact $K$ and every $b \ge 1$ there is $C$ with $\bigl\| W_v(\mathrm{archRealLift3}(\mathrm{diag}(y_1y_2,y_2,1)) \cdot k) - \sum_{i,j} cv_{ij}(y_2,k)\, y_1^{e_i} (\log y_1)^j \bigr\| \le C y_1^{\rho+\delta}$ for $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$, where $W_v$ is `whittaker3` for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` (additive measure: adelic Haar measure conditioned on the adelic box, the $\mathrm{GL}_2$ data being irrelevant) and the character $\psi_{\mathbb Q}$, i.e. the triple integral of $v(u(x,y,z)g)\psi_{\mathbb Q}(-(x+y))$ over the upper unipotent; (iii) each $cv'_{iji'j'}$ is continuous; (iv) for every compact $K$ there is $C$ with $\bigl\| cv_{ij}(y_2,k) - \sum_{i',j'} cv'_{iji'j'}(k)\, y_2^{e_{i'}} (\log y_2)^{j'} \bigr\| \le C y_2^{\rho+\delta}$ for $k \in K$, $0 < y_2 \le 1$. Then for every $k' \in \mathrm{GL}_3(\mathbb A_{\mathbb Q})$ the same four clauses hold with the same $\rho,\delta,e$ for the right translate $g \mapsto v(gk')$, with coefficients $(y,k) \mapsto cv_{ij}(y,kk')$ and $k \mapsto cv'_{iji'j'}(kk')$.
--
--   This records that the four-clause joint exponent–logarithm expansion of a Whittaker function along the archimedean torus of $\mathrm{GL}_3$ is stable under right translation of the underlying function, the coefficients being translated accordingly. It is used in the cubic-induction arguments to show that the relevant spaces of leading coefficients are right-translation stable, and is cited by [`LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule`](thm.html#LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule) and [`LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top`](thm.html#LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.joint_expansion_comp_mul_right
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp :
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (k' : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (fun i j y k => cv i j y (k * k')) i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun g => v (g * k'))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, (fun i j y k => cv i j y (k * k')) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous ((fun i j i' j' k => cv' i j i' j' (k * k')) i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖(fun i j y k => cv i j y (k * k')) i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, (fun i j i' j' k => cv' i j i' j' (k * k')) i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)) := by sorry
