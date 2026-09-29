-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
-- name    : LanglandsTunnell.CubicInduction.hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b5e732fa-5e72-5e40-8a85-2a120e004f63
-- title:
--   Double-slot coefficients intertwine the archimedean flow derivative
-- statement:
--   Fix a function $v$ on the adelic group $GL_3(\mathbb{A}_{\mathbb{Q}})$ with complex values, and write $W(\varphi)$ for its Whittaker transform `whittaker3` with respect to the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` and the standard character `psiQ`, i.e. the triple iterated integral of $\varphi(\mathrm{u}(x,y,z)g)\,\psi(-(x+y))$ against the additive Haar measure of $\mathbb{A}_{\mathbb{Q}}$ conditioned on the adelic box, where $\mathrm{u}(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$. It is assumed that: $v$ is archimedean-smooth in the sense of `IsArchSmooth3` (for every $g$ the map $e \mapsto v(g\cdot \mathrm{lift}(e))$ on real $3\times 3$ matrices is $C^\infty$ on $\{\det e \neq 0\}$, $\mathrm{lift}$ being `archRealLift3`, the adelic unit attached to a real matrix at the infinite place); $W(v)$ is likewise archimedean-smooth; every iterated right-derivative word $\mathrm{archDeriv}\,i_1j_1\cdots$ applied to $v$ is continuous; and $v$ is left invariant under the rational points $GL_3(\mathbb{Q})$. Fix $c,d \in \{0,1,2\}$, a real $\rho$, naturals $n, J$, an injective family of exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$ with $\mathrm{Re}\,e_i \le \rho$, and $\delta > 0$. Let $(cv, cv')$ and $(dv, dv')$ be joint-expansion data, for $W(v)$ and for $W(\mathrm{archDeriv}\,c\,d\,v)$ respectively: the first-slot coefficients $cv\,i\,j$ (resp. $dv\,i\,j$) are continuous on $\{y_1 > 0\}\times GL_3(\mathbb{A}_{\mathbb{Q}})$ and, uniformly for $k$ in a compact set and $y_2$ in a range $[b^{-1},b]$, approximate the function $y_1 \mapsto W(\cdot)(\mathrm{lift}(\mathrm{diag}(y_1y_2,y_2,1))\cdot k)$ by $\sum_{i,j} cv\,i\,j\,y_2\,k \cdot y_1^{e_i}(\log y_1)^j$ with error $O(y_1^{\rho+\delta})$ for $0 < y_1 \le 1$; the second-slot coefficients $cv'$ (resp. $dv'$) are continuous and, uniformly for $k$ in a compact set and for all index pairs, approximate $cv\,i\,j\,y_2\,k$ by $\sum_{i',j'} cv'\,i\,j\,i'\,j'\,k \cdot y_2^{e_{i'}}(\log y_2)^{j'}$ with error $O(y_2^{\rho+\delta})$ for $0 < y_2 \le 1$. The conclusion is that for all indices $i,j,i',j'$ and every $k \in GL_3(\mathbb{A}_{\mathbb{Q}})$, the function $s \mapsto cv'\,i\,j\,i'\,j'\,(k\cdot\mathrm{lift}(1 + sE_{cd}))$ of a real variable has derivative $dv'\,i\,j\,i'\,j'\,k$ at $s = 0$, in the sense of `HasDerivAt`.
--
--   This identifies the doubly iterated leading coefficients of the two-variable $y^{e}(\log y)^{j}$ expansion of a Whittaker coefficient as an equivariant invariant: differentiating the coefficient of $v$ along the one-parameter unipotent flow $1+sE_{cd}$ at the infinite place returns the corresponding coefficient of $\mathrm{archDeriv}\,c\,d\,v$, slot by slot with no mixing between logarithmic powers. It is used to equip the map sending a form to its double-slot coefficient functions with a Lie-algebra action, in the construction of the submodule and induced-picture packages of the cubic-induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
    (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hv : WhittakerBlock.IsArchSmooth3 v ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ v) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) v wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), v (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = v g)
    (c d : Fin 3)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (he : Function.Injective e) (hre : ∀ i, (e i).re ≤ ρ)
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
    (dv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (dv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexpd :
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => dv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv c d v)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, dv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (dv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖dv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, dv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) :
    ∀ (i : Fin n) (j : Fin J) (i' : Fin n) (j' : Fin J) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      HasDerivAt
        (fun s : ℝ => cv' i j i' j' (k * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
        (dv' i j i' j' k) 0 := by sorry
