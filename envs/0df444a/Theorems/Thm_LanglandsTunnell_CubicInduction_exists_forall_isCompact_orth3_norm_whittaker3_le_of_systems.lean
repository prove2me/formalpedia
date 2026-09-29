-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems
-- name    : LanglandsTunnell.CubicInduction.exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/226b00de-eda4-5de9-824a-d8900ad0d063
-- title:
--   Two-variable Whittaker decay on GL₃ from regular-singular systems
-- statement:
--   Fix reals $\theta<\theta_0$ and naturals $N,d,d_2,d',d_2',D,D'$. The assertion is that there exists a natural number $N'$ such that the following holds for all finite sets $\iota,\iota'\subset\mathbb C$ and all polynomials $q,q'\in\mathbb C[X]$ that are nonzero, of degrees at most $D$ and $D'$, and each of whose roots has the form $e_0+j$ with $e_0\in\iota$ (resp. $\iota'$) and $j$ a natural number, and for every function $u:\mathrm{GL}_3(\mathbb A_{\mathbb Q})\to\mathbb C$. Throughout, $W(\Phi)(g)$ denotes `whittaker3` for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` and the standard character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), i.e. the triple integral of $\Phi(u(x,y,z)g)\psi(-(x+y))$ over $x,y,z$ against the adelic additive Haar measure conditioned on the box (infinite box times integral finite adeles), $u(x,y,z)$ being the upper unipotent matrix with entries $x,y,z$; $t(y_1,y_2)$ denotes [`WhittakerBlock.archRealLift3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) of the real diagonal matrix $\mathrm{diag}(y_1y_2,y_2,1)$; a word $w$ in $\mathrm{Fin}\,3\times\mathrm{Fin}\,3$ acts on $u$ by the iterated archimedean derivatives `WhittakerBlock.archDeriv` taken by `List.foldr`; and $k$ is orthogonal at infinity when `archComponent3` of $k$ lies in `orth3`, i.e. its archimedean matrix $A$ satisfies $A^{\mathsf T}A=1$. Assume three hypotheses. (i) System hypothesis: there are $r$, words $w_0,\dots,w_r$ with $w_0$ empty, elements $\kappa_0=1,\dots,\kappa_r$ trivial at every finite place and orthogonal at infinity, continuous families $g\mapsto Mc(g)_b$ ($b\le d_2$) and $g\mapsto Mc'(g)_a$ ($a\le d_2'$) of $(r+1)\times(r+1)$ complex matrices, and continuous families of continuous linear operators $A(g)_{k,b}$ ($k<d$, $b\le d_2$), $A'(g)_{k,a}$ ($k<d'$, $a\le d_2'$) on $\mathbb C^{r+1}$, such that for every $g_0$ orthogonal at infinity: $q$ annihilates $\sum_b z^b Mc(g_0)_b$ for all $z>0$, $q'$ annihilates $\sum_a y^a Mc'(g_0)_a$ for all $y>0$, and for every $F:\mathbb R\times\mathbb R\to\mathbb C^{r+1}$ whose $i$-th component at $(y,z)$ is $W$ of the $w_i$-derivative of $u$ evaluated at $t(y,z)g_0\kappa_i$, one has $F(y,z)_0=W(u)(t(y,z)g_0)$ and there exist $F_y,F_z$ with, for $y,z>0$, $\partial_y F=F_y$ and $y\,F_y=\bigl(\sum_b z^b Mc(g_0)_b\bigr)F+\sum_{k<d}\sum_b y^{k+1}z^b A(g_0)_{k,b}F$, and symmetrically $\partial_z F=F_z$ with $z\,F_z=\bigl(\sum_a y^a Mc'(g_0)_a\bigr)F+\sum_{k<d'}\sum_a z^{k+1}y^a A'(g_0)_{k,a}F$. (ii) A priori bound: for every word $w$ and every compact $K$ there is $C$ with $\|W(\text{$w$-derivative of }u)(t(y_1,y_2)k)\|\le C(\max(y_1,1)\max(y_2,1)\max(y_1^{-1},1)\max(y_2^{-1},1))^N$ for $k\in K$, $y_1,y_2>0$. (iii) Ray-wise decay: for every $k$ orthogonal at infinity, for each fixed $y_2>0$ there is $C$ with $\|W(g\mapsto u(gk))(t(y_1,y_2))\|\le C y_1^{\theta_0}$ for $0<y_1\le1$, and symmetrically in the two variables. Conclusion: for every compact set $K$ all of whose elements are orthogonal at infinity there is a constant $C$ with $\|W(u)(t(y_1,y_2)k)\|\le C\,(\min(y_1,1)^{\theta}\max(y_1,1)^{N'})(\min(y_2,1)^{\theta}\max(y_2,1)^{N'})$ for all $k\in K$ and all $y_1,y_2>0$.
--
--   This is the two-variable regime split for Whittaker coefficients on $\mathrm{GL}_3$ over $\mathbb Q$: a uniform bound with decay exponent $\theta$ in each small variable and a loss exponent $N'$ depending only on the numerical data, obtained from a regular-singular first-order system in the two diagonal parameters together with an a priori polynomial bound and decay along each coordinate ray. It is deduced from the two `RegularSingular` estimates for such systems, and feeds the diagonal Whittaker bound [`LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder`](thm.html#LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder) in the cubic-induction strand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems
    (θ₀ θ : ℝ) (hθ : θ < θ₀) (N : ℕ) (d d₂ d' d₂' D D' : ℕ) :
    ∃ N' : ℕ,
      ∀ (ι ι' : Finset ℂ) (q q' : Polynomial ℂ),
      (q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ D ∧ q'.natDegree ≤ D' ∧
      (∀ e : ℂ, q.IsRoot e → ∃ e₀ ∈ ι, ∃ j : ℕ, e = e₀ + j) ∧
      (∀ e : ℂ, q'.IsRoot e → ∃ e₀ ∈ ι', ∃ j : ℕ, e = e₀ + j)) →
      ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
        (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ κ 0 = 1 ∧
        (∀ i, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (κ i) = 1) ∧
          archComponent3 (𝓞 ℚ) ℚ (κ i) ∈ orth3) ∧
        (∀ b, Continuous fun g => Mc g b) ∧ (∀ a, Continuous fun g => Mc' g a) ∧
        (∀ k b, Continuous fun g => A g k b) ∧ (∀ k a, Continuous fun g => A' g k a) ∧
        ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g₀ a) q' = 0) ∧
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ
              (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
          (∀ y z : ℝ, F y z 0 =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀)) ∧
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g₀ k a (F y z))
      ) →
      (∀ w : List (Fin 3 × Fin 3),
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N) →
      (∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
        (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀)) →
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
        (∀ k ∈ K, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) →
        ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
            C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by sorry
