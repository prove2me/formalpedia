-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/bbfd018e-399c-578d-acc0-691f06d70aca
-- title:
--   A separated sign-projection read forces p=0
-- statement:
--   Fix a complex subspace $M$ of the space of functions $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ (the group being `AdelicGL 3 (𝓞 ℚ) ℚ`, the units of $3\times 3$ matrices over the adele ring of $\mathbb{Q}$) and a central character $\omega\colon \mathbb{A}_{\mathbb{Q}}^{\times}\to\mathbb{C}^{\times}$. Throughout, `whittaker3` denotes the Whittaker transform $W\Phi(g)=\int\!\!\int\!\!\int \Phi(u(x,y,z)g)\,\psi(-(x+y))$, the three integrals being taken against the additive adelic Haar measure conditioned on the adelic box, with $\psi$ the standard additive character of $\mathbb{A}_{\mathbb{Q}}$; `archRealLift3 e` is the element of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ attached to a real $3\times 3$ matrix $e$ (the identity when $\det e=0$); `archDeriv i j φ` is $g\mapsto \frac{d}{ds}\varphi\bigl(g\cdot\mathrm{archRealLift3}(1+sE_{ij})\bigr)\big|_{s=0}$; `casimir2` and `casimir3` are the operators $\varphi\mapsto\sum_{i,j}\partial_{ij}\partial_{ji}\varphi$ and $\varphi\mapsto\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}\varphi$ built from these derivatives; `IsArchSmooth3 φ` says that for every $g$ the map $e\mapsto\varphi(g\cdot\mathrm{archRealLift3}\,e)$ is $C^{\infty}$ on $\{\det e\neq 0\}$; `orth3` is the set of $k\in\mathrm{GL}_3$ over the infinite adeles with $k^{\mathsf T}k=1$; and `gauge3` $g=\max(1,\,\mathrm{archGauge3}(g)\cdot\mathrm{finGauge3}(g))$.
--
--   The standing hypotheses on $M$ are: `h1` (automorphic regularity): every $w\in M$ is archimedean smooth, its Whittaker transform is archimedean smooth, every iterated archimedean derivative $\partial_{i_1j_1}\cdots\partial_{i_rj_r}w$ is continuous, and $w$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$; `h3` ($K$-finiteness): for each $w\in M$ there is a finite set $s$ of functions such that for every $k$ with trivial components at all height-one primes and archimedean component in `orth3` the right translate $g\mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$; `h4`: these right translates lie in $M$; `h5`: $M$ is stable under each $\partial_{ij}$; `h10`: there exists a pairing $B$ on $M$ which is Hermitian, linear in its first argument, has $\mathrm{Re}\,B(w,w)>0$ for $0\neq w\in M$, makes each $\partial_{ij}$ skew ($B(\partial_{ij}w,w')=-B(w,\partial_{ij}w')$) and is invariant under right translation by the $k$ just described; `h11`: there are monic polynomial relations for the three Casimir operators, i.e. natural numbers $N_1,N_2,N_3$ and coefficients $a_1,a_2,a_3$ with top coefficient $1$ such that $\sum_l a_r(l)\,\mathrm{casimir}_r^{\,l}w=0$ on $M$ for $r=1,2,3$; `h12`: every $v\in M$ transforms under the central adelic scalars by $\omega$; `h13`: every $v\in M$ has moderate growth, i.e. there is $N$ such that each iterated derivative of $v$ is bounded by $C\cdot\mathrm{gauge3}^N$.
--
--   In addition, concrete monic relations are fixed: $N_2$, $a_2$ with $a_2(N_2)=1$, $N_3$, $a_3$ with $a_3(N_3)=1$, and `hrel` asserting $\sum_l a_2(l)\,\mathrm{casimir2}^{\,l}w=0$ and $\sum_l a_3(l)\,\mathrm{casimir3}^{\,l}w=0$ for all $w\in M$.
--
--   The asymptotic data consist of a real $\rho$, natural numbers $n,J$, an injective family of exponents $e\colon\mathrm{Fin}\,n\to\mathbb{C}$ with $\mathrm{Re}\,e_i\le\rho$, and $\delta>0$. The hypothesis `hexp` (summarised here) requires that for every $N$ and every function $u$ enjoying the regularity, left $\mathrm{GL}_3(\mathbb{Q})$-invariance, $\omega$-central character, archimedean smoothness, $K$-finiteness, the two Casimir relations for $a_2,a_3$, and the growth bound with exponent $N$, the Whittaker function of $u$ along the diagonal elements $\mathrm{diag}(y_1y_2,y_2,1)$ admits two iterated expansions in the monomials $y^{e_i}(\log y)^{j}$, one in $y_1$ with coefficients $c_{ij}(y_2,k)$ continuous on $\{y_2>0\}$ and error $O(y_1^{\rho+\delta})$ uniformly for $k$ in compacta and $y_2$ in $[b^{-1},b]$, whose coefficients in turn expand in $y_2$ with continuous coefficients $c'_{iji'j'}(k)$ and error $O(y_2^{\rho+\delta})$, together with a cascade clause (if all $c_{i''j''}$ with $\mathrm{Re}\,e_{i''}<\mathrm{Re}\,e_i$ vanish and all $c'_{iji'j'}$ vanish, then $c_{ij}$ vanishes); and likewise with the roles of $y_1$ and $y_2$ interchanged.
--
--   Indices $i_9,i_9'\in\mathrm{Fin}\,n$ and $j_0,j_0'\in\mathrm{Fin}\,J$ are fixed. The spectral parameter is of unitary shape: reals $\sigma,\sigma_3$, distinct nonzero indices $b_0\neq c_0$ in $\mathrm{Fin}\,3$, and $\nu\colon\mathrm{Fin}\,3\to\mathbb{C}$ with $\nu_0=-\tfrac12+i\sigma$, $\nu_{b_0}=\tfrac12+i\sigma$, $\nu_{c_0}=i\sigma_3$.
--
--   A $\mathbb{C}$-linear map $\Lambda\colon M\to(\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C})$ is given, subject to three hypotheses: `hΛa` says that for every $v\in M$ and every pair of families $(c_v,c_v')$ satisfying the four expansion clauses in the first variable (continuity of $c_v$ on $\{y_2>0\}$, the $O(y_1^{\rho+\delta})$ approximation of the Whittaker function of $v$ on $\mathrm{diag}(y_1y_2,y_2,1)k$, continuity of $c_v'$, and the $O(y_2^{\rho+\delta})$ approximation of $c_v$), one has $\Lambda v(k)=c'_{v,i_9j_0i_9'j_0'}(k)$ for all $k$ — thus $\Lambda$ reads off one fixed double coefficient; `hΛb` says $\Lambda$ commutes with right translation by any $k'$ with trivial finite components and archimedean component in `orth3`; `hΛc` says that for $v\in M$ and $c,d\in\mathrm{Fin}\,3$ the function $s\mapsto \Lambda v\bigl(g\cdot\mathrm{archRealLift3}(1+sE_{cd})\bigr)$ has derivative $\Lambda(\partial_{cd}v)(g)$ at $s=0$.
--
--   Finally, a sign character $\varepsilon\colon\mathrm{Fin}\,3\to\mathrm{Fin}\,2$ is given, an element $k_1$ whose archimedean component is $1$, a natural number $\ell$ and a polynomial $p\in\mathbb{C}[X_0,X_1,X_2]$ homogeneous of degree $\ell$, with the case hypothesis `hcls`: either $\ell=0$ and $\varepsilon_0=\varepsilon_{b_0}=\varepsilon_{c_0}$, or $\ell=1$ and $\varepsilon_0=\varepsilon_{b_0}\neq\varepsilon_{c_0}$. A subspace $M'\le M$ is given which is stable under right translation by the $k$ as above (`hK`) and under all $\partial_{ij}$ (`hD`), such that (`hEq`) for every $u\in M'$, every upper-triangular $t$ (that is, $t_{ij}=0$ for $j<i$) with positive diagonal and every $g$,
--   $$\Lambda u(\mathrm{archRealLift3}(t)\,g)=\Bigl(\prod_{a}t_{aa}^{\,\nu_a+(1,0,-1)_a}\Bigr)\Lambda u(g),$$
--   and such that (`hsep`) the sign projection separates $M'$ on $O(3)k_1$: if $u\in M'$ and for every real $o$ with $\sum_a o_{ai}o_{aj}=\delta_{ij}$ one has
--   $$\tfrac18\sum_{\tau\in\{0,1\}^3}(-1)^{\sum_a \varepsilon_a\tau_a}\,\Lambda u\bigl(\mathrm{archRealLift3}(\mathrm{diag}((-1)^{\tau_a}))\cdot \mathrm{archRealLift3}(o)\,k_1\bigr)=0,$$
--   then $u=0$. The last hypothesis concerns a member $v'\in M'$ whose projected read is given by $p$ (`hread'`): for every real $o$ with $\sum_a o_{ai}o_{aj}=\delta_{ij}$,
--   $$\tfrac18\sum_{\tau\in\{0,1\}^3}(-1)^{\sum_a \varepsilon_a\tau_a}\,\Lambda v'\bigl(\mathrm{archRealLift3}(\mathrm{diag}((-1)^{\tau_a}))\cdot\mathrm{archRealLift3}(o)\,k_1\bigr)=\det(o)^{(\ell+\sum_a\varepsilon_a)\bmod 2}\cdot p\bigl(o_{00},o_{10},o_{20}\bigr),$$
--   the evaluation being that of $p$ at the entries of the zeroth column of $o$.
--
--   Under all these hypotheses the conclusion is that $p=0$.
--
--   This is the non-genericity step in the archimedean analysis of the cubic induction for Langlands–Tunnell on $\mathrm{GL}_3$: at the reducibility point $\nu_{b_0}-\nu_0=1$ the bottom $O(3)$-type of the induced representation lies in the degenerate constituent, which is annihilated by the quantised $2\times 2$ minor and therefore carries no Whittaker model, so the polynomial recording that type must vanish. It is used by the two companion results treating the homogeneous cases of degree $0$ and degree $1$ separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule
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
    (i9 i9' : Fin n) (j₀ j₀' : Fin J)
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hΛa : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
        (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
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
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) →
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ k = cv' i9 j₀ i9' j₀' k))
    (hΛb : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k')))
    (hΛc : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0))
    (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hcls : (ℓ = 0 ∧ ε 0 = ε b₀ ∧ ε 0 = ε c₀) ∨ (ℓ = 1 ∧ ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀))
    (M' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hle : M' ≤ M)
    (hK : (∀ w ∈ M', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M'))
    (hD : (∀ w ∈ M', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M'))
    (hEq : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'), (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hle hu⟩ g))
    (hsep : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'),
        (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) → u = 0)
    (v' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv' : v' ∈ M')
    (hread' : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v', hle hv'⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) :
    p = 0 := by sorry
