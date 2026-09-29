-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_families_ne_bot_of_inducedPicture_package_top
-- name    : LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/8b5ef48c-db11-5590-a8b3-0a8cd7e71274
-- title:
--   Transition-stable harmonic families from an induced-picture package
-- statement:
--   Throughout, $G$ denotes the adelic group `AdelicGL 3 (𝓞 ℚ) ℚ`, i.e. $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$, and $W_u$ denotes the Whittaker transform `whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ u`, that is, the triple integral $\int\!\int\!\int u(n(x,y,z)\,g)\,\psi_{\mathbb{Q}}(-(x+y))$ against the conditional additive Haar measure attached to the adelic box, $n(x,y,z)$ running over the upper unipotent subgroup. `archDeriv i j` is the right-invariant derivative at the identity in the direction of the elementary matrix $E_{ij}$ placed at the archimedean place, `casimir1`, `casimir2`, `casimir3` are the associated traces $\sum_i D_{ii}$, $\sum_{i,j}D_{ij}D_{ji}$, $\sum_{i,j,k}D_{ij}D_{jk}D_{ki}$, `IsArchSmooth3 φ` asserts that for every $g$ the function $e\mapsto \varphi(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on the locus $\det e\neq 0$, `orth3` is the set of $k$ in $\mathrm{GL}_3$ of the infinite adeles with $k^{\mathsf T}k=1$, and `gauge3` is the height $\max(1,\text{archimedean gauge}\cdot\text{finite gauge})$.
--
--   The data are: a $\mathbb{C}$-subspace $M$ of functions $G\to\mathbb{C}$ and a character $\omega$ of the idele class group of $\mathbb{Q}$ (a homomorphism $(\mathbb{A}_{\mathbb{Q}})^{\times}\to\mathbb{C}^{\times}$).
--
--   The hypotheses on $M$ (the smoothing-module package) are: `h1`, every $w\in M$ is arch-smooth, its Whittaker transform $W_w$ is arch-smooth, every iterated archimedean derivative $\mathrm{archDeriv}\,i_1j_1\cdots$ along a finite list of index pairs is continuous, and $w$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$ under `globalPointsGL`; `h3`, for every $w\in M$ there is a finite set $s$ of functions such that all right translates $g\mapsto w(gk)$, for $k$ with trivial component at every height-one prime and archimedean component in `orth3`, lie in the span of $s$; `h4`, $M$ is stable under those same right translations; `h5`, $M$ is stable under each $\mathrm{archDeriv}\,i\,j$; `h10`, existence of a pairing $B$ on functions which, on $M$, is hermitian-symmetric, $\mathbb{C}$-linear in its first argument, satisfies $\operatorname{Re}B(w,w)>0$ for $0\neq w\in M$, makes each $\mathrm{archDeriv}\,i\,j$ skew ($B(D_{ij}w,w')=-B(w,D_{ij}w')$), and is invariant under the right translations above; `h11`, existence of monic relations in the three Casimir operators, i.e. of $N_1,N_2,N_3$ and coefficient vectors $a_1,a_2,a_3$ with last entry $1$ such that $\sum_l a_t(l)\,\mathrm{casimir}_t^{[l]}w=0$ for $t=1,2,3$ and all $w\in M$; `h12`, the central character law $v(\mathrm{centralScalarGL}(z)\,g)=\omega(z)v(g)$ for $v\in M$; and `h13`, moderate growth: for each $v\in M$ there is $N$ such that every iterated archimedean derivative of $v$ is bounded by $C\cdot\mathrm{gauge3}(g)^N$ for a constant depending on the list of directions.
--
--   In addition a distinguished pair of monic Casimir relations is given explicitly: $N_2$, $a_2:\mathrm{Fin}(N_2+1)\to\mathbb{C}$ with $a_2(N_2)=1$, $N_3$, $a_3$ with $a_3(N_3)=1$, and `hrel`, which asserts $\sum_l a_2(l)\,\mathrm{casimir2}^{[l]}w=0$ and $\sum_l a_3(l)\,\mathrm{casimir3}^{[l]}w=0$ for all $w\in M$.
--
--   The expansion data are a real number $\rho$, naturals $n,J$, an injective $e:\mathrm{Fin}\,n\to\mathbb{C}$ (`he`) with $\operatorname{Re}e(i)\le\rho$ for all $i$ (`hre`), and $\delta>0$. The hypothesis `hexp` is a joint asymptotic-expansion principle: for every natural $N$ and every function $u:G\to\mathbb{C}$ such that all iterated archimedean derivatives of $u$ are continuous, $u$ is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, $u$ transforms under the centre by $\omega$, $u$ is arch-smooth, the right translates of $u$ by the $k$ described above lie in the span of a fixed finite set, $u$ satisfies the two monic relations with coefficients $a_2$ and $a_3$, and every iterated derivative of $u$ is bounded by $C\cdot\mathrm{gauge3}(g)^N$, the following two conclusions hold. First, there are coefficients $c:\mathrm{Fin}\,n\to\mathrm{Fin}\,J\to\mathbb{R}\to G\to\mathbb{C}$, each $(y,g)\mapsto c_{ij}(y,g)$ continuous on $\{y>0\}\times G$, such that for every compact $K\subseteq G$ and every $b\ge 1$ there is $C$ with
--   $$\Big\|W_u\big(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\big)-\sum_{i,j}c_{ij}(y_2,k)\,y_1^{e(i)}(\log y_1)^{j}\Big\|\le C\,y_1^{\rho+\delta}$$
--   for $k\in K$, $b^{-1}\le y_2\le b$ and $0<y_1\le 1$; moreover there are secondary coefficients $c'_{i j i' j'}:G\to\mathbb{C}$, all continuous, such that for every compact $K$ there is $C$ with $\|c_{ij}(y_2,k)-\sum_{i',j'}c'_{iji'j'}(k)\,y_2^{e(i')}(\log y_2)^{j'}\|\le C\,y_2^{\rho+\delta}$ for $k\in K$ and $0<y_2\le 1$, and a cascade clause: for each $(i,j)$, if $c_{i''j''}$ vanishes identically (for all $y_2>0$ and all $k$) for every $i''$ with $\operatorname{Re}e(i'')<\operatorname{Re}e(i)$ and all $j''$, and if all $c'_{iji'j'}$ vanish, then $c_{ij}$ vanishes identically. Second, the same statement with the roles of $y_1$ and $y_2$ interchanged (expansion in $y_2\to0$ with coefficients depending on $y_1$, their expansion in $y_1\to0$, and the corresponding cascade clause).
--
--   Further data: slot indices $i_9,i_9'\in\mathrm{Fin}\,n$ and logarithmic indices $j_0,j_0'\in\mathrm{Fin}\,J$; Casimir scalars $\lambda_1,\lambda_2,\lambda_3\in\mathbb{C}$; reals $\sigma,\sigma_3$; indices $b_0,c_0\in\mathrm{Fin}\,3$ with $b_0\neq 0$, $c_0\neq 0$, $b_0\neq c_0$ (`hb₀`, `hc₀`, `hbc`); and $\nu:\mathrm{Fin}\,3\to\mathbb{C}$ subject to the unitary shape $\nu_0=-\tfrac12+\sigma i$ (`hν0`), $\nu_{b_0}=\tfrac12+\sigma i$ (`hνb`), $\nu_{c_0}=\sigma_3 i$ (`hνc`), and to the identification `hνD`: $\nu=(e(i_9)-1,\;e(i_9')-e(i_9),\;\lambda_1-e(i_9')+1)$.
--
--   Finally a function $F:G\to\mathbb{C}$, a $\mathbb{C}$-subspace $V$ of functions on $G$, and an element $k_1\in G$ are given, and `hV` is the induced-picture package, a conjunction of the following clauses: $F\in V$; the archimedean component of $k_1$ is $1$; there is a real $3\times3$ matrix $o$ with $\sum_a o_{ai}o_{aj}=\delta_{ij}$ and $F(\mathrm{archRealLift3}\,o\cdot k_1)\neq0$; every $G\in V$ is continuous; every $G\in V$ is arch-smooth and is a joint Casimir eigenfunction, $\mathrm{casimir}_tG=\lambda_tG$ for $t=1,2,3$; every $G\in V$ satisfies the Borel equivariance $G(\mathrm{archRealLift3}\,t\cdot g)=\big(\prod_a t_{aa}^{\nu_a+u_a}\big)G(g)$ for all upper-triangular $t$ with positive diagonal, where $u=(1,0,-1)$; $V$ is stable under right translation by the $k'$ with trivial components at all height-one primes and archimedean component in `orth3`; those translates of any $G\in V$ lie in the span of a finite set depending on $G$; $V$ is closed under the infinitesimal right flows, i.e. for all $G\in V$ and all indices $c,d$ there is $G'\in V$ with $G'(g)$ the derivative at $s=0$ of $s\mapsto G(g\cdot\mathrm{archRealLift3}(1+sE_{cd}))$; and the double-coefficient realisation: every $G\in V$ arises as $G=cv'_{i_9 j_0 i_9' j_0'}$ for some $v\in M$ together with expansion data $cv,cv'$ satisfying the first half of the expansion in `hexp` (continuity of $cv_{ij}$ on $\{y_2>0\}\times G$, the remainder bound $C\,y_1^{\rho+\delta}$ uniformly for $k$ in compacta and $y_2\in[b^{-1},b]$, continuity of the $cv'$, and the remainder bound $C\,y_2^{\rho+\delta}$ for the $y_2$-expansion of the $cv_{ij}$).
--
--   The conclusion is stated after introducing four operators on polynomials in $\mathbb{C}[X_0,X_1,X_2]=$ `MvPolynomial (Fin 3) ℂ`: the matrix-valued $\Xi$, sending $\nu$ and $p$ to the $3\times3$ matrix with diagonal entries $2(\nu_c+u_c)\,p$ (again $u=(1,0,-1)$) and off-diagonal entries $-\big(X_{\max(c,d)}\partial_{\min(c,d)}p-X_{\min(c,d)}\partial_{\max(c,d)}p\big)$; $\mathrm{lower}_2(A)=\sum_{c,d}\partial_c\partial_d A_{cd}$; $\mathrm{lower}_1(A)=\sum_{a,b,c,d}\tfrac{(a-c)(c-d)(d-a)}{2}\,X_c\,\partial_b\partial_d A_{ab}$, the scalars being the images of the indices in $\mathbb{C}$; and $\mathrm{same}_2(A)=6T-\big(\sum_iX_i^2\big)\sum_i\partial_i^2T$ where $T=\sum_{c,d}X_c\,\partial_dA_{cd}$.
--
--   The assertion is that there exist two families $S,S':\mathbb{N}\to\{\mathbb{C}\text{-subspaces of }\mathbb{C}[X_0,X_1,X_2]\}$ such that all of the following hold simultaneously: every $p\in S_\ell$ is homogeneous of degree $\ell$ and harmonic, $\sum_i\partial_i^2p=0$; $S_0\le\langle 1\rangle$; $S_1=0$; $S_2\le\langle X_0^2-X_2^2,\;X_1^2-X_2^2\rangle$; for every $\ell$ and every $p\in S_\ell$, $\mathrm{lower}_2(\Xi(\nu,p))\in S_{\ell-2}$ and $\mathrm{lower}_1(\Xi(\nu,p))\in S_{\ell-1}$, the subtractions being truncated in $\mathbb{N}$; for every $p\in S_2$, $\mathrm{same}_2(\Xi(\nu,p))\in S_2$; $S_0=0$; every $p\in S'_\ell$ is homogeneous of degree $\ell$ and harmonic; $S'_0=0$; $S'_1\le\langle X_{c_0}\rangle$; $S'_2\le\langle X_0X_{b_0}\rangle$; for every $\ell$ and every $p\in S'_\ell$, $\mathrm{lower}_2(\Xi(\nu,p))\in S'_{\ell-2}$ and $\mathrm{lower}_1(\Xi(\nu,p))\in S'_{\ell-1}$; and $S'_1=0$. Together with this conjunction the conclusion asserts the disjunction that $S_\ell\neq0$ for some $\ell$ or $S'_\ell\neq0$ for some $\ell$.
--
--   Note that the degree bounds and the vanishing statements are asserted jointly, not as alternatives indexed by a sign type: both families are required to vanish in degrees $0$ and $1$ (so the clauses $S_0\le\langle1\rangle$ and $S'_1\le\langle X_{c_0}\rangle$ are subsumed), while one of them must be non-zero in some degree.
--
--   This is the second disjunct of the dichotomy for the leading Whittaker coefficient of a smoothing module on $\mathrm{GL}_3$ over $\mathbb{Q}$, in the archimedean analysis underlying the cubic induction step of Langlands–Tunnell: from an induced-picture package with unitary Borel parameter $\nu$ it produces families of harmonic homogeneous polynomials, stable under the transition operators of the compact picture, with trivial bottom degrees but non-trivial somewhere. It is used by [`LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re`](thm.html#LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re), where the resulting configuration is what is eventually excluded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_families_ne_bot_of_inducedPicture_package_top.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top
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
        G = cv' i9 j₀ i9' j₀'))) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    ∃ S S' : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      ((∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} ∧
          (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) ∧
          (∀ p ∈ S 2, same₂ (Ξ ν p) ∈ S 2) ∧
          S 0 = ⊥ ∧
          (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S' ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S' 0 = ⊥ ∧
          S' 1 ≤ Submodule.span ℂ {(MvPolynomial.X c₀ : MvPolynomial (Fin 3) ℂ)} ∧
          S' 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X b₀ : MvPolynomial (Fin 3) ℂ)} ∧
          (∀ ℓ, ∀ p ∈ S' ℓ, lower₂ (Ξ ν p) ∈ S' (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S' (ℓ - 1)) ∧
          S' 1 = ⊥) ∧
      ((∃ ℓ, S ℓ ≠ ⊥) ∨ (∃ ℓ, S' ℓ ≠ ⊥)) := by sorry
