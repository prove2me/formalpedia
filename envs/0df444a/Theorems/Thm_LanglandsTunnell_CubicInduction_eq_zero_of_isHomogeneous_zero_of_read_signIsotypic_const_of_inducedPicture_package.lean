-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_isHomogeneous_zero_of_read_signIsotypic_const_of_inducedPicture_package
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_isHomogeneous_zero_of_read_signIsotypic_const_of_inducedPicture_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/bb3d4557-8645-593b-a346-0b685807d1d0
-- title:
--   Vanishing of degree-zero reads in a constant sign class
-- statement:
--   Throughout, functions on the adelic group $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, written `AdelicGL 3 (𝓞 ℚ) ℚ`, are complex valued, and `whittaker3` denotes the triple unipotent integral
--   $$\Phi \mapsto \Big(g \mapsto \int\!\!\int\!\!\int \Phi(u_3(x,y,z)\,g)\,\psi(-(x+y))\Big)$$
--   formed with the pin data `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, whose additive measure is the adelic additive Haar measure conditioned on the adelic box $\{x : x_\infty \in \mathrm{infiniteBox},\ x_{\mathrm{fin}} \text{ integral}\}$, and with $\psi$ the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615). Here [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) is the adelic point attached to a real $3\times 3$ matrix $e$ (the identity when $e$ is singular), `WhittakerBlock.archDeriv i j` is differentiation at $s=0$ of $g \mapsto \varphi(g\cdot \exp\text{-type lift of } I + s E_{ij})$, `WhittakerBlock.casimir1`, `casimir2`, `casimir3` are the traces $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ of these derivations, [`WhittakerBlock.IsArchSmooth3 φ`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) says that for every $g$ the map $e \mapsto \varphi(g\cdot \text{lift}(e))$ is $C^\infty$ on $\{\det e \neq 0\}$, `orth3` is the set of $k$ with $k^{\mathsf T}k = 1$ over the infinite adeles, and `gauge3 ℚ g` $= \max(1, \mathrm{archGauge}\cdot\mathrm{finGauge})$.
--
--   The data are: a $\mathbb{C}$-submodule $M$ of functions on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ and a character $\omega : \mathbb{A}_\mathbb{Q}^\times \to \mathbb{C}^\times$, subject to the *smoothing-module hypotheses*: `h1` (each $w \in M$ is archimedean-smooth, its Whittaker integral is archimedean-smooth, all iterated `archDeriv` of $w$ are continuous, and $w$ is left invariant under the global points $\mathrm{GL}_3(\mathbb{Q})$); `h3` (for each $w \in M$ a finite set $s$ of functions such that every right translate $g \mapsto w(gk)$ by a $k$ with trivial components at all finite places and archimedean component in `orth3` lies in the span of $s$); `h4` (such right translates stay in $M$); `h5` ($M$ is stable under all nine `archDeriv i j`); `h10` (existence of a form $B$ which is Hermitian on $M$, linear in its first argument, satisfies $0 < \mathrm{Re}\,B(w,w)$ for $0 \neq w \in M$, makes each `archDeriv i j` skew, and is invariant under the right translations just described); `h11` (monic polynomial relations: degrees $N_1,N_2,N_3$ and coefficient families with top coefficient $1$ annihilating every $w \in M$ when applied to the iterates of `casimir1`, `casimir2`, `casimir3` respectively); `h12` (central character: $v(z\cdot g) = \omega(z)v(g)$ for $v \in M$); and `h13` (gauge growth: for each $v \in M$ an exponent $N$ such that every iterated `archDeriv` of $v$ is bounded by $C\cdot \text{gauge3}(g)^N$ for some constant depending on the derivative word).
--
--   In addition there are fixed monic relation data: $N_2$, $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ with $a_2(\text{last}) = 1$, $N_3$, $a_3$ with $a_3(\text{last}) = 1$, and `hrel`, asserting that $\sum_l a_2(l)\,\mathrm{casimir2}^{(l)}w = 0$ and $\sum_l a_3(l)\,\mathrm{casimir3}^{(l)}w = 0$ for all $w \in M$.
--
--   The *expansion data* are a real $\rho$, naturals $n, J$, an injective family of exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$ with $\mathrm{Re}\,e(i) \le \rho$ for all $i$, and $\delta > 0$; the hypothesis `hexp` asserts that for every exponent $N$ and every function $u$ which has continuous iterated `archDeriv`, is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, has central character $\omega$, is archimedean-smooth, is finite under the right translations above, satisfies the two monic Casimir relations with $a_2$ and $a_3$, and obeys the gauge bound with exponent $N$, the Whittaker integral of $u$ admits two iterated expansions along the torus directions $\mathrm{diag}(y_1y_2, y_2, 1)$: in the first, coefficients $c_{i j}(y_2, k)$ jointly continuous on $\{y_2 > 0\}$ with, for each compact $K$ and each $b \ge 1$, a constant $C$ bounding
--   $$\Big\| \mathrm{whittaker3}(u)\big(\mathrm{lift}(\mathrm{diag}(y_1y_2,y_2,1))\,k\big) - \sum_{i,j} c_{ij}(y_2,k)\, y_1^{e_i}(\log y_1)^{j}\Big\| \le C\,y_1^{\rho+\delta}$$
--   for $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$; together with continuous secondary coefficients $c'_{i j i' j'}(k)$ expanding each $c_{ij}(y_2,k)$ in $y_2^{e_{i'}}(\log y_2)^{j'}$ with remainder $C y_2^{\rho+\delta}$ uniformly on compacta for $0 < y_2 \le 1$, and a vanishing clause: if for a pair $(i,j)$ all $c_{i''j''}$ with $\mathrm{Re}\,e_{i''} < \mathrm{Re}\,e_i$ vanish identically and all $c'_{i j i' j'}$ vanish, then $c_{ij}$ vanishes. The second expansion is the same statement with the roles of $y_1$ and $y_2$ interchanged.
--
--   Further data: indices $i_9, i_9' \in \mathrm{Fin}\,n$, $j_0, j_0' \in \mathrm{Fin}\,J$, Casimir eigenvalues $\lambda_1,\lambda_2,\lambda_3 \in \mathbb{C}$, reals $\sigma, \sigma_3$, indices $b_0, c_0 \in \mathrm{Fin}\,3$ with $b_0 \neq 0$, $c_0 \neq 0$, $b_0 \neq c_0$, and a parameter $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$ of unitary shape, namely $\nu_0 = -1/2 + \sigma i$, $\nu_{b_0} = 1/2 + \sigma i$, $\nu_{c_0} = \sigma_3 i$, and simultaneously $\nu = (e_{i_9} - 1,\ e_{i_9'} - e_{i_9},\ \lambda_1 - e_{i_9'} + 1)$.
--
--   Finally a function $F$, a submodule $V$, a point $k_1$, and the nine-clause *induced-picture package* `hV`: $F \in V$; the archimedean component of $k_1$ is trivial; there is an orthogonal real matrix $o$ (i.e. $\sum_a o_{ai}o_{aj} = \delta_{ij}$) with $F(\mathrm{lift}(o)\,k_1) \neq 0$; every $G \in V$ is continuous; every $G \in V$ is archimedean-smooth and satisfies $\mathrm{casimir1}\,G = \lambda_1 G$, $\mathrm{casimir2}\,G = \lambda_2 G$, $\mathrm{casimir3}\,G = \lambda_3 G$; every $G \in V$ transforms under left multiplication by upper-triangular real matrices $t$ with positive diagonal by the factor $\prod_a (t_{aa})^{\nu_a + (1,0,-1)_a}$; $V$ is stable under right translation by $k'$ with trivial finite components and archimedean component in `orth3`, and each $G \in V$ is finite under such translations in the span of a finite set; $V$ is closed under the one-parameter right derivatives in each of the nine matrix directions (the derivative of $s \mapsto G(g\cdot\mathrm{lift}(I + sE_{ab}))$ at $0$ is again a member of $V$); and every $G \in V$ is a double leading coefficient of a member of $M$ at the slots $(i_9,j_0,i_9',j_0')$, that is $G = c'_{i_9 j_0 i_9' j_0'}$ for some $v \in M$ carrying expansion data $c, c'$ with the continuity and the two asymptotic bounds of the first expansion above.
--
--   The last data are a sign character $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ and a submodule $V_\varepsilon$ with the eight-clause package `hVε`: continuity of its members; archimedean smoothness together with the same three Casimir eigenvalues $\lambda_1,\lambda_2,\lambda_3$; the same left transformation law under upper-triangular $t$ with the parameter $\nu$; stability and finiteness under right translation by the $k'$ as above; closure under the nine one-parameter right derivatives; sign isotypy, namely $G(\mathrm{lift}(\mathrm{diag}((-1)^{\sigma_a}))\,g) = (-1)^{\sum_a \varepsilon_a\sigma_a}G(g)$ for every $\sigma : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$; and provenance from $V$, namely each $G \in V_\varepsilon$ equals $\tfrac18\sum_\sigma (-1)^{\sum_a \varepsilon_a\sigma_a}\,G'(\mathrm{lift}(\mathrm{diag}((-1)^{\sigma_a}))\,g)$ for some $G' \in V$. The hypothesis `hI` requires the sign character to be constant on the three distinguished indices: $\varepsilon_0 = \varepsilon_{b_0}$ and $\varepsilon_0 = \varepsilon_{c_0}$.
--
--   Under all of this, the conclusion asserts: for every $p \in \mathbb{C}[X_0,X_1,X_2]$ which is homogeneous of degree $0$, if there exists $G \in V_\varepsilon$ such that for every real $3\times 3$ matrix $o$ with $\sum_a o_{ai}o_{aj} = \delta_{ij}$ one has
--   $$\det\big((o_{ij})_{ij}\big)^{(0 + \sum_a \varepsilon_a) \bmod 2}\cdot \big(p(X_0,X_1,X_2) \text{ evaluated with } X_a \mapsto o_{a0}\big) = G(\mathrm{lift}(o)\,k_1),$$
--   the substitution being the algebra map sending $X_a$ to the variable indexed $(a,0)$ followed by evaluation of the doubly indexed variables at the entries of $o$, then $p = 0$.
--
--   This is the degree-zero ("bottom") case of the vanishing dichotomy for the sign-isotypic components of the space of double leading Whittaker coefficients in the cubic-induction argument: in the constant sign class $\varepsilon_0 = \varepsilon_{b_0} = \varepsilon_{c_0}$, corresponding to the trivial and determinant $O(3)$-types, no non-zero constant can be read off a member of $V_\varepsilon$ on the orthogonal translates of $k_1$ with the determinant twist $(\sum_a \varepsilon_a) \bmod 2$. It rests on the construction of the double-slot coefficient map out of the smoothing module, on the separating stable submodule it produces, and on the vanishing statement for reads of sign projections, and is used in turn by [`LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_isHomogeneous_zero_of_read_signIsotypic_const_of_inducedPicture_package.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_isHomogeneous_zero_of_read_signIsotypic_const_of_inducedPicture_package
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
    (hI : ε 0 = ε b₀ ∧ ε 0 = ε c₀) :
    ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous 0 →
      (∃ G ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((0 + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
            (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
          G (WhittakerBlock.archRealLift3 o * k₁)) →
      p = 0 := by sorry
