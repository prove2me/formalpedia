-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_isHomogeneous_one_of_read_signIsotypic_linear_of_inducedPicture_package
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_isHomogeneous_one_of_read_signIsotypic_linear_of_inducedPicture_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/816fd837-b05b-5607-9641-82e2e9480f56
-- title:
--   No non-zero linear form is read in the split sign class
-- statement:
--   The setting is the space of complex-valued functions on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$, written `AdelicGL 3 (𝓞 ℚ) ℚ`. Fixed are a complex subspace $M$ of such functions and a character $\omega$ of the idele class group $(\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$. Throughout, $k$ ranges over elements of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ whose component `componentAt3` at every height-one prime of $\mathbb{Z}$ is trivial and whose archimedean component `archComponent3` lies in `orth3`, i.e. satisfies $k^{\mathsf T}k = 1$ over the infinite adele ring; `archRealLift3 e` denotes the element of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ attached to a real $3\times 3$ matrix $e$, `archDeriv i j` the right derivative at the identity in the direction of the $(i,j)$ elementary matrix, `casimir1`, `casimir2`, `casimir3` the traces $\sum_i D_{ii}$, $\sum_{i,j} D_{ij}D_{ji}$, $\sum_{i,j,k} D_{ij}D_{jk}D_{ki}$ of these derivations, `gauge3` the gauge $\max(1, \text{arch}\cdot\text{fin})$, and `whittaker3` the triple integral of a function against $\psi(-(x+y))$ over the upper unipotent coordinates $x,y,z$, taken for the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) and the pin data `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, whose relevant content is the conditional additive Haar measure on the adelic box.
--
--   The hypotheses on $M$ are: `h1`, that every $w \in M$ is archimedean smooth in the sense of [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) (for each $g$, $e \mapsto w(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on the locus of invertible $e$), that its Whittaker integral is again archimedean smooth, that every iterated right derivative of $w$ along a finite word of index pairs is continuous, and that $w$ is invariant under left translation by the rational points `globalPointsGL 3 (𝓞 ℚ) ℚ γ`, $\gamma \in \mathrm{GL}_3(\mathbb{Q})$; `h3`, that each $w \in M$ is $\mathrm{O}(3)$-finite, i.e. admits a finite set $s$ of functions such that all right translates $g \mapsto w(gk)$, for $k$ as above, lie in the $\mathbb{C}$-span of $s$; `h4`, that $M$ is stable under these right translations; and `h5`, that $M$ is stable under the nine derivations `WhittakerBlock.archDeriv i j`.
--
--   Further: `h10` posits a form $B$ on functions which, restricted to $M$, is Hermitian symmetric, linear in its first argument, positive in the sense that $0 < \operatorname{Re} B(w,w)$ for $0 \neq w \in M$, makes each `archDeriv i j` skew, and is invariant under the simultaneous right translation of both arguments by $k$ as above. `h11` posits natural numbers $N_1,N_2,N_3$ and coefficient families $a_1,a_2,a_3$ with last coefficient $1$ such that $\sum_l a_i(l)\,\mathrm{casimir}_i^{[l]}w = 0$ on $M$ for $i = 1,2,3$, where $\mathrm{casimir}_i^{[l]}$ is the $l$-fold iterate. `h12` says each $v \in M$ has central character $\omega$: $v(z\cdot g) = \omega(z)v(g)$ for central scalars `centralScalarGL 3 (𝓞 ℚ) ℚ z`. `h13` says each $v \in M$ admits an exponent $N$ such that every iterated derivative of $v$ along a word is bounded by $C\cdot \mathrm{gauge3}(g)^N$ for some constant.
--
--   Independently of `h11`, explicit data $N_2, a_2$ with $a_2(\mathrm{last}) = 1$ and $N_3, a_3$ with $a_3(\mathrm{last}) = 1$ are given, together with `hrel`, the assertion that the corresponding two monic relations in `casimir2` and `casimir3` hold on all of $M$. Expansion data consist of a real $\rho$, natural numbers $n, J$, an injective family of exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$ with $\operatorname{Re}(e\,i) \le \rho$ for all $i$, and a positive real $\delta$. The hypothesis `hexp` is the joint asymptotic expansion input: for every $N$ and every function $u$ which has continuous iterated derivatives along all words, is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, has central character $\omega$, is archimedean smooth, is $\mathrm{O}(3)$-finite in the span sense above, satisfies the two monic Casimir relations given by $a_2$ and $a_3$, and satisfies the gauge bound of order $N$ along every word, two expansion packages exist. In the first, there are coefficient functions $c\, i\, j\, y\, k$, continuous on $\{y > 0\}$ jointly in $(y,k)$, such that on every compact set of $k$'s and every band $b^{-1} \le y_2 \le b$ ($b \ge 1$) the Whittaker integral of $u$ at $\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2, y_2, 1)\cdot k$ differs from $\sum_{i,j} c\,i\,j\,y_2\,k \cdot y_1^{e\,i}(\log y_1)^{j}$ by at most $C\,y_1^{\rho+\delta}$ for $0 < y_1 \le 1$; there are moreover continuous secondary coefficients $c'\,i\,j\,i'\,j'\,k$ with $c\,i\,j\,y_2\,k$ approximated by $\sum_{i',j'} c'\,i\,j\,i'\,j'\,k\cdot y_2^{e\,i'}(\log y_2)^{j'}$ to within $C\,y_2^{\rho+\delta}$ uniformly on compacta for $0 < y_2 \le 1$; and a minimality clause: for each $(i,j)$, if all $c\,i''\,j''$ with $\operatorname{Re}(e\,i'') < \operatorname{Re}(e\,i)$ vanish identically and all $c'\,i\,j\,i'\,j'$ vanish, then $c\,i\,j$ vanishes. The second package is the same statement with the roles of $y_1$ and $y_2$ interchanged (expansion first in $y_2$, then in $y_1$).
--
--   The parameter data are indices $i9, i9' \in \mathrm{Fin}\,n$ and $j_0, j_0' \in \mathrm{Fin}\,J$, Casimir eigenvalues $\lambda_1, \lambda_2, \lambda_3 \in \mathbb{C}$, reals $\sigma, \sigma_3$, indices $b_0, c_0 \in \mathrm{Fin}\,3$ with $b_0 \neq 0$, $c_0 \neq 0$, $b_0 \neq c_0$, and an exponent vector $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$ of unitary shape $\nu_0 = -\tfrac12 + \sigma i$, $\nu_{b_0} = \tfrac12 + \sigma i$, $\nu_{c_0} = \sigma_3 i$, subject also to $\nu = (e\,i9 - 1,\; e\,i9' - e\,i9,\; \lambda_1 - e\,i9' + 1)$. Given further a function $F$, a subspace $V$, and an element $k_1$, the hypothesis `hV` (nine clauses) requires: $F \in V$; $k_1$ has trivial archimedean component; there is a real orthogonal matrix $o$ (i.e. $\sum_a o_{ai}o_{aj} = \delta_{ij}$) with $F(\mathrm{archRealLift3}\,o\cdot k_1) \neq 0$; every $G \in V$ is continuous; every $G \in V$ is archimedean smooth and an eigenvector of `casimir1`, `casimir2`, `casimir3` with eigenvalues $\lambda_1, \lambda_2, \lambda_3$; every $G \in V$ transforms under left multiplication by $\mathrm{archRealLift3}\,t$, for $t$ upper triangular with positive diagonal, by the factor $\prod_a (t_{aa})^{\nu_a + (1,0,-1)_a}$; $V$ is stable under the right translations by $k'$ as above; every $G \in V$ is $\mathrm{O}(3)$-finite in the span sense; $V$ is stable under the nine right derivatives, expressed as: for each $G \in V$ and each pair of indices (the Lean binders here reuse the name $c_0$ for a fresh index) there is $G' \in V$ with $s \mapsto G(g\cdot\mathrm{archRealLift3}(1 + s E_{ab}))$ having derivative $G'(g)$ at $0$ for all $g$; and finally every $G \in V$ arises as a double leading coefficient of a member of $M$: there are $v \in M$ and expansion data $cv, cv'$ satisfying the continuity, band-uniform $y_1$-expansion bound with error $C\,y_1^{\rho+\delta}$, continuity of $cv'$ and $y_2$-expansion bound with error $C\,y_2^{\rho+\delta}$ exactly as in the first package of `hexp`, such that $G = cv'\,i9\,j_0\,i9'\,j_0'$.
--
--   Finally a sign character $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ and a subspace $V_\varepsilon$ are given, with `hVε` (eight clauses): continuity of every $G \in V_\varepsilon$; archimedean smoothness together with the same three Casimir eigenvalues $\lambda_1, \lambda_2, \lambda_3$; the same upper-triangular transformation law with exponents $\nu_a + (1,0,-1)_a$; stability under the right translations by $k'$; $\mathrm{O}(3)$-finiteness; stability under the nine right derivatives in the `HasDerivAt` form, with the derivative again in $V_\varepsilon$; $\varepsilon$-isotypy under the diagonal sign matrices, namely $G(\mathrm{archRealLift3}\,\mathrm{diag}((-1)^{\sigma_a})\cdot g) = (-1)^{\sum_a \varepsilon_a\sigma_a}G(g)$ for every $\sigma : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ (this binder reuses the name $\sigma$); and provenance from $V$: every $G \in V_\varepsilon$ equals the $\varepsilon$-sign projection $g \mapsto \tfrac18\sum_\sigma (-1)^{\sum_a \varepsilon_a\sigma_a} F(\mathrm{archRealLift3}\,\mathrm{diag}((-1)^{\sigma_a})\cdot g)$ of some $F \in V$. The hypothesis `hII` fixes the sign class: $\varepsilon_0 = \varepsilon_{b_0}$ and $\varepsilon_0 \neq \varepsilon_{c_0}$.
--
--   The conclusion is that for every polynomial $p \in \mathbb{C}[X_0,X_1,X_2]$ which is homogeneous of degree $1$, if there exists $G \in V_\varepsilon$ such that for every real orthogonal $o$ (i.e. $\sum_a o_{ai}o_{aj} = \delta_{ij}$) one has
--   $$\det\big((o_{ij})\big)^{(1+\sum_a \varepsilon_a)\bmod 2}\cdot p(o_{00}, o_{10}, o_{20}) = G(\mathrm{archRealLift3}\,o\cdot k_1),$$
--   where the left-hand side is the evaluation at the entries of $o$ of the image of $p$ under the substitution $X_a \mapsto X_{(a,0)}$ into the polynomial ring in the matrix variables, then $p = 0$.
--
--   This is the degree-one (lowest $\mathrm{O}(3)$-type) vanishing clause of the type dichotomy for the sign class $\varepsilon_0 = \varepsilon_{b_0} \neq \varepsilon_{c_0}$ at the unitary reducible parameter $\nu_0 = -\tfrac12+i\sigma$, $\nu_{b_0} = \tfrac12+i\sigma$, $\nu_{c_0} = i\sigma_3$: no non-zero linear form in the first column of an orthogonal matrix, twisted by $\det^{(1+\sum_a\varepsilon_a)\bmod 2}$, is realised on the orthogonal translates of $k_1$ by a member of the sign-isotypic space $V_\varepsilon$ of double leading Whittaker coefficients. It is used by [`LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top) in the archimedean part of the cubic induction, and it invokes the double-slot coefficient, separating-submodule and read-vanishing statements of the same development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_isHomogeneous_one_of_read_signIsotypic_linear_of_inducedPicture_package.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_isHomogeneous_one_of_read_signIsotypic_linear_of_inducedPicture_package
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
    (hII : ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀) :
    ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous 1 →
      (∃ G ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((1 + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
            (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
          G (WhittakerBlock.archRealLift3 o * k₁)) →
      p = 0 := by sorry
