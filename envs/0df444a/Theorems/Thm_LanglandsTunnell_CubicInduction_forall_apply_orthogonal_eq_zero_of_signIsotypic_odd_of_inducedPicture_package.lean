-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package
-- name    : LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/e022b307-b776-568f-ae5e-d4431895001f
-- title:
--   Odd sign classes: vanishing of sign-isotypic leading coefficients
-- statement:
--   Throughout, $G$-valued functions are complex-valued functions on the adelic group $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, written `AdelicGL 3 (𝓞 ℚ) ℚ`; `archRealLift3 e` denotes the adelic point attached to a real $3\times 3$ matrix $e$ (its unit if $e$ is invertible, and $1$ otherwise), `orth3` is the set of $k \in \mathrm{GL}_3$ of the infinite adele ring with $k^{\mathsf T}k = 1$, `archDeriv i j` is the right derivative at $s=0$ along the one-parameter family $1 + s E_{ij}$, `casimir1`, `casimir2`, `casimir3` are the operators $\sum_i D_{ii}$, $\sum_{i,j} D_{ij}D_{ji}$, $\sum_{i,j,k} D_{ij}D_{jk}D_{ki}$ built from these derivatives, `IsArchSmooth3 φ` says that for every $g$ the map $e \mapsto φ(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on the locus $\det e \neq 0$, `gauge3 ℚ` is the adelic gauge $\max(1, \text{arch}\cdot\text{finite})$, and `whittaker3` applied to the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` and to the standard additive character $\psi_{\mathbb{Q}}$ is the triple integral $\iiint Φ(u_3(x,y,z)g)\,\psi_{\mathbb{Q}}(-(x+y))$ against the adelic additive Haar measure conditioned on the adelic box.
--
--   The data are: a $\mathbb{C}$-submodule $M$ of functions on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and a character $ω$ of the adelic ideles.
--
--   The smoothing-module package consists of eight hypotheses. `h1`: every $w \in M$ is archimedean-smooth, its Whittaker transform (for the pins and character above) is archimedean-smooth, all iterated `archDeriv` derivatives of $w$ along arbitrary lists of index pairs are continuous, and $w$ is invariant under left translation by the global points of $\mathrm{GL}_3(\mathbb{Q})$. `h3`: each $w \in M$ is finite in the sense that some finite set of functions spans all right translates $g \mapsto w(gk)$ with $k$ having trivial component at every height-one prime of $\mathbb{Z}$ and archimedean component in `orth3`. `h4`: $M$ is stable under these right translations. `h5`: $M$ is stable under the nine operators `archDeriv i j`. `h10`: there exists a form $B$ on pairs of functions which, on $M$, is Hermitian-symmetric, additive and $\mathbb{C}$-linear in its first slot, satisfies $0 < \operatorname{Re} B(w,w)$ for $w \neq 0$, makes each `archDeriv i j` skew, and is invariant under the right translations just described. `h11`: there exist $N_1,N_2,N_3$ and monic coefficient families $a_1,a_2,a_3$ (value $1$ at `Fin.last`) such that each of the three associated polynomial expressions in the iterates of `casimir1`, `casimir2`, `casimir3` annihilates every $w \in M$. `h12`: every $v \in M$ has central character $ω$ for the scalar embedding `centralScalarGL`. `h13`: each $v \in M$ admits an exponent $N$ such that every iterated derivative of $v$ is bounded by a constant times $\mathrm{gauge3}_{\mathbb{Q}}(g)^N$.
--
--   Next come the two distinguished monic relations: naturals $N_2, N_3$ with coefficient families $a_2 : \mathrm{Fin}(N_2+1) \to \mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1) \to \mathbb{C}$ normalised by $a_2(\text{last}) = a_3(\text{last}) = 1$, and `hrel` asserting that the corresponding polynomials in `casimir2` and in `casimir3` kill every $w \in M$.
--
--   The expansion data are a real $ρ$, naturals $n$ and $J$, an injective family of exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$ with $\operatorname{Re} e_i \le ρ$ for all $i$, and a real $δ > 0$. The hypothesis `hexp` is a uniform joint-expansion principle: for every natural $N$ and every function $u$ all of whose iterated derivatives are continuous, which is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, has central character $ω$, is archimedean-smooth, is finite in the above spanning sense, satisfies both monic Casimir relations with $a_2$ and $a_3$, and obeys the gauge bound with exponent $N$, there hold two symmetric conclusions. In the first, there are coefficients $c : \mathrm{Fin}\,n \to \mathrm{Fin}\,J \to \mathbb{R} \to (\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C})$, continuous on $\{y > 0\}$ jointly in the real parameter and the group variable, such that for every compact $K$ and every $b \ge 1$ some constant $C$ bounds, for $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$, the difference between the Whittaker transform of $u$ at $\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2, y_2, 1)\cdot k$ and $\sum_{i,j} c_{ij}(y_2,k)\, y_1^{e_i}(\log y_1)^j$ by $C y_1^{ρ+δ}$; moreover there are continuous second-layer coefficients $c'$ with, for each compact $K$, a constant bounding $\lVert c_{ij}(y_2,k) - \sum_{i',j'} c'_{ij i'j'}(k)\, y_2^{e_{i'}}(\log y_2)^{j'}\rVert$ by $C y_2^{ρ+δ}$ for $0 < y_2 \le 1$, and a cascade clause: for each $(i,j)$, if $c_{i''j''}$ vanishes identically for all $(i'',j'')$ with $\operatorname{Re} e_{i''} < \operatorname{Re} e_i$ and all $c'_{ij i'j'}$ vanish identically, then $c_{ij}$ vanishes identically on $y_2 > 0$. The second conclusion is the same statement with the roles of $y_1$ and $y_2$ exchanged.
--
--   Further data: indices $i_9, i_9' \in \mathrm{Fin}\,n$ and $j_0, j_0' \in \mathrm{Fin}\,J$; Casimir eigenvalues $λ_1, λ_2, λ_3 \in \mathbb{C}$; reals $σ, σ_3$; indices $b_0, c_0 \in \mathrm{Fin}\,3$ with $b_0 \neq 0$, $c_0 \neq 0$, $b_0 \neq c_0$; and a parameter $ν : \mathrm{Fin}\,3 \to \mathbb{C}$ of unitary shape, $ν_0 = -\tfrac12 + σ i$, $ν_{b_0} = \tfrac12 + σ i$, $ν_{c_0} = σ_3 i$, which is moreover required to equal the explicit vector $(e_{i_9} - 1,\; e_{i_9'} - e_{i_9},\; λ_1 - e_{i_9'} + 1)$.
--
--   Finally there are a function $F$, a submodule $V$, an adelic point $k_1$, and the induced-picture package `hV`, a nine-fold conjunction: $F \in V$; the archimedean component of $k_1$ is trivial; some real matrix $o$ with $\sum_a o_{ai}o_{aj} = δ_{ij}$ satisfies $F(\mathrm{archRealLift3}\,o \cdot k_1) \neq 0$; every member of $V$ is continuous; every member is archimedean-smooth and an eigenvector of `casimir1`, `casimir2`, `casimir3` with eigenvalues $λ_1, λ_2, λ_3$; every member transforms under left multiplication by $\mathrm{archRealLift3}\,t$ with $t$ upper triangular and positive diagonal by the factor $\prod_a t_{aa}^{\,ν_a + (1,0,-1)_a}$; $V$ is stable under right translation by $k'$ with trivial finite components and archimedean component in `orth3`; each member of $V$ is finite in the spanning sense for such translates; for each member and each pair of indices the right derivative along $1 + sE$ exists pointwise with derivative again in $V$; and each $G \in V$ arises as a double leading coefficient, namely there are $v \in M$ and expansion families $c_v, c_v'$ satisfying the continuity and the two approximation bounds of order $ρ+δ$ (in $y_1$ for the Whittaker transform of $v$, and in $y_2$ for $c_v$) with $G = c_v'(i_9, j_0, i_9', j_0')$.
--
--   The last data are a sign character $ε : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ and a submodule $V_ε$ subject to the eight-fold package `hVε`: every member of $V_ε$ is continuous; every member is archimedean-smooth with the same three Casimir eigenvalues $λ_1, λ_2, λ_3$; every member obeys the same triangular transformation law with exponents $ν_a + (1,0,-1)_a$; $V_ε$ is stable under right translation by $k'$ with trivial finite components and orthogonal archimedean component; each member is finite in the spanning sense; each member has right derivatives in $V_ε$ along all $1 + sE_{c_0 d_0}$; each member is $ε$-isotypic for the diagonal sign matrices, $G(\mathrm{archRealLift3}\,\mathrm{diag}((-1)^{σ_a}) \cdot g) = (-1)^{\sum_a ε_a σ_a} G(g)$; and each $G \in V_ε$ comes from some $F' \in V$ by the projection formula $G(g) = \tfrac18 \sum_{σ} (-1)^{\sum_a ε_a σ_a} F'(\mathrm{archRealLift3}\,\mathrm{diag}((-1)^{σ_a}) \cdot g)$. The final hypothesis `hodd` is $ε_0 \neq ε_{b_0}$.
--
--   Under all of this, the conclusion is that for every $G \in V_ε$ and every real $3 \times 3$ matrix $o$ with $\sum_a o_{ai} o_{aj} = δ_{ij}$ for all $i,j$, one has $G(\mathrm{archRealLift3}\,o \cdot k_1) = 0$.
--
--   This is the archimedean non-occurrence step in the cubic-induction analysis for Langlands–Tunnell: when the sign character $ε$ has the wrong parity at the pair of coordinates where the principal-series parameter satisfies $ν_0 - ν_{b_0} = -1$, the $ε$-isotypic part of the space of double leading Whittaker coefficients reads as zero on the whole orthogonal orbit through $k_1$. It is used by [`LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top), and it is proved by combining the passage from the smoothing module to a polynomial model carrying a positive skew-invariant form with the polynomial-side vanishing statement for odd sign classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (h5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h10 :
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (h11 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0))
    (h12 :
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g))
    (h13 :
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N))
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (hrel : ∀ w ∈ M,
      (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧ (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ) (he : Function.Injective e)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hexp : ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0)))
    (i9 i9' : Fin n) (j₀ j₀' : Fin J) (lam₁ lam₂ lam₃ : ℂ)
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I) (hνD : ν = (![e i9 - 1, e i9' - e i9, lam₁ - e i9' + 1] : Fin 3 → ℂ))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hV : (F ∈ V ∧
      archComponent3 (𝓞 ℚ) ℚ k₁ = 1 ∧
      (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧
        F (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) ∧
      (∀ G ∈ V, Continuous G) ∧
      (∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ V, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ V, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ V) ∧
      (∀ G ∈ V, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ V, ∃ v ∈ M, ∃ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
          (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
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
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)) ∧
        G = cv' i9 j₀ i9' j₀')))
    (ε : Fin 3 → Fin 2) (Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hVε : (∀ G ∈ Vε, Continuous G) ∧
      (∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε) ∧
      (∀ G ∈ Vε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)))
    (hodd : ε 0 ≠ ε b₀) :
    ∀ G ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      G (WhittakerBlock.archRealLift3 o * k₁) = 0 := by sorry
