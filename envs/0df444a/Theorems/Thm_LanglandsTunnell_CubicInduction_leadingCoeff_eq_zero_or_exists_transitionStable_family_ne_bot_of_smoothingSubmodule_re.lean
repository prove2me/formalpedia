-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re
-- name    : LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1e0b0ba3-a587-58d7-bb2b-f28dca185d24
-- title:
--   Vanishing leading coefficient, or transition-stable harmonic families
-- statement:
--   Fix natural numbers $m$ and $J$ with $J>0$, an injective family of exponents $e \colon \mathrm{Fin}\,m \to \mathbb{C}$ all of whose members satisfy $\tfrac12 \le \operatorname{Re} e_i$ (hypothesis `hre`), a homomorphism $\omega$ from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$, a real $\tau > \tfrac12$, and an index $i_0$ with $\operatorname{Re} e_{i_0} = \tfrac12$. Fix further a $\mathbb{C}$-submodule $M$ of the space of functions $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ (here $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ is `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group over the adele ring of $\mathbb{Q}$), and a map $A$ assigning to a function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ a function of a real parameter $y_2$ and a point $k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$.
--
--   Throughout, `WhittakerBlock.archDeriv i j φ` is the derivative at $s=0$ of $s \mapsto \varphi(g \cdot \mathrm{lift}(1 + sE_{ij}))$, where $\mathrm{lift} =$ [`WhittakerBlock.archRealLift3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) sends a real $3\times 3$ matrix to the corresponding archimedean point of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ when it is invertible and to $1$ otherwise; `casimir1`, `casimir2`, `casimir3` are the traces $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ of these derivations; `IsArchSmooth3 φ` says that for every $g$ the function $e \mapsto \varphi(g\cdot\mathrm{lift}(e))$ is $C^\infty$ on the set of real $3\times 3$ matrices of nonzero determinant; `whittaker3` applied to the pin data `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` and the standard additive character `psiQ` is the triple integral $\iiint \varphi(u_3(x,y,z)g)\,\psi(-(x+y))$ over the upper unipotent coordinates with respect to the adelic additive Haar measure conditioned on the adelic box (the infinite box times the integral finite adeles); `orth3` is the set of $k$ with $k^{\mathsf T}k = 1$ over the infinite adeles; `componentAt3 p` and `archComponent3` are the projections to the place $p$ and to the archimedean component; `gauge3 ℚ g` is $\max(1, \text{archimedean gauge} \cdot \text{finite gauge})$; and `globalPointsGL`, `centralScalarGL` are the embeddings of $\mathrm{GL}_3(\mathbb{Q})$ and of the central ideles.
--
--   The hypotheses on $M$ and $A$ are: `h1`, that every $w \in M$ is archimedean-smooth, its Whittaker integral is archimedean-smooth, every iterated derivative $\partial_{i_1j_1}\cdots\partial_{i_rj_r} w$ along a finite word of pairs (the empty word giving $w$ itself) is continuous, and $w$ is left invariant under $\mathrm{GL}_3(\mathbb{Q})$; `h2`, that there are degrees $N_1,N_2,N_3$ and coefficient families $a_1,a_2,a_3$ with top coefficient $1$ such that for every $w \in M$ the three monic polynomial relations $\sum_l a_k(l)\,\mathrm{casimir}_k^{[l]}$ annihilate the Whittaker integral of $w$; `h3`, that for every $w \in M$ there is a finite set $s$ of functions such that for all $k$ trivial at every finite place and with orthogonal archimedean component the right translate $g \mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$; `h4`, that for such $k$ the right translate of $w \in M$ again lies in $M$ and satisfies $A(g \mapsto w(g k))\,y_2\,k' = A\,w\,y_2\,(k'k)$ for all $y_2$ and $k'$; `h5`, that $M$ is stable under the nine derivations $\partial_{ij}$; `h6`, that $A$ is $\mathbb{C}$-linear in its function argument on $M$, i.e. $A(z\cdot w_1 + w_2) = z\,A w_1 + A w_2$ pointwise for $w_1, w_2 \in M$; `h7`, that for every $w \in M$ there is a family $b_{ij}(y_2,k)$ indexed by $i \in \mathrm{Fin}\,m$, $j \in \mathrm{Fin}\,J$, jointly continuous on $\{y_2 > 0\}$, with $b_{i_0 j}(y_2,k) = A\,w\,y_2\,k$ for the slot $j$ of value $0$ and all $y_2>0$ and all $k$, such that for every compact $K$ and every bound $\mathrm{bd} \ge 1$ there is $C$ with
--   $$\Bigl\| W_w\bigl(\mathrm{lift}(\mathrm{diag}(y_1y_2, y_2, 1))\,k\bigr) - \sum_{i}\sum_{j} b_{ij}(y_2,k)\, y_1^{e_i} (\log y_1)^{j}\Bigr\| \le C\, y_1^{\tau}$$
--   for all $k \in K$, all $y_2 \in [\mathrm{bd}^{-1}, \mathrm{bd}]$ and all $0 < y_1 \le 1$, where $W_w$ denotes the Whittaker integral of $w$; `h8`, that for $w \in M$ and all $i,j$ the function $s \mapsto A\,w\,y_2\,(k\cdot\mathrm{lift}(1 + sE_{ij}))$ has derivative $A(\partial_{ij}w)\,y_2\,k$ at $s=0$; `h9`, that for $w \in M$ and $c_1 < c_2$ the function $s \mapsto A\,w\,y_2\,(k \cdot \mathrm{lift}(r_{c_1c_2}(s)))$, with $r_{c_1c_2}(s)$ the rotation by $s$ in the $(c_1,c_2)$-plane, has derivative $A(\partial_{c_2c_1}w)\,y_2\,k - A(\partial_{c_1c_2}w)\,y_2\,k$ at $s = 0$; `h10`, that there is a form $B$ on pairs of functions which on $M$ is Hermitian, linear in its first argument, positive in the sense that $\operatorname{Re} B(w,w) > 0$ for $0 \ne w \in M$, makes each $\partial_{ij}$ skew ($B(\partial_{ij}w, w') = -B(w, \partial_{ij}w')$), and is invariant under simultaneous right translation by $k$ trivial at the finite places with orthogonal archimedean component; `h11`, the same shape of monic relations as `h2` but imposed on the members $w \in M$ themselves rather than on their Whittaker integrals; `h12`, that every $v \in M$ has central character $\omega$, i.e. $v(\mathrm{diag}(z,z,z)\,g) = \omega(z)\,v(g)$; and `h13`, that every $v \in M$ admits an exponent $N$ such that for each word in the pairs $(i,j)$ there is $C$ with $\|\partial_{i_1j_1}\cdots\partial_{i_rj_r}v(g)\| \le C\,\mathrm{gauge3}(g)^N$ for all $g$.
--
--   The conclusion uses four operators on $3\times 3$ matrices of polynomials in $\mathbb{C}[X_0,X_1,X_2]$, introduced as local definitions. For $\nu \in \mathbb{C}^3$ and $p$ a polynomial, $\Xi(\nu,p)$ is the matrix whose $(c,c)$ entry is $2(\nu_c + \delta_c)\,p$ with $\delta = (1,0,-1)$, and whose $(c,d)$ entry for $c \ne d$ is $-\bigl(X_{\max(c,d)}\,\partial_{\min(c,d)}p - X_{\min(c,d)}\,\partial_{\max(c,d)}p\bigr)$. Then $\mathrm{lower}_2(\mathcal{M}) = \sum_{c,d}\partial_c\partial_d(\mathcal{M}_{cd})$; $\mathrm{lower}_1(\mathcal{M}) = \sum_{a,b,c,d} \frac{(a-c)(c-d)(d-a)}{2}\,X_c\,\partial_b\partial_d(\mathcal{M}_{ab})$, the indices being read as complex numbers through their natural-number values; and $\mathrm{same}_2(\mathcal{M}) = 6\,Q - \bigl(\sum_i X_i^2\bigr)\bigl(\sum_i \partial_i^2 Q\bigr)$ where $Q = \sum_{c,d} X_c\,\partial_d(\mathcal{M}_{cd})$.
--
--   The assertion is a disjunction. Either $A\,w\,y_2\,k = 0$ for every $w \in M$, every $y_2 > 0$ and every $k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$; or there exist real numbers $\sigma, \sigma_3$, giving the two spectral parameters $\nu_{12} = (-\tfrac12 + \sigma i,\ \tfrac12 + \sigma i,\ \sigma_3 i)$ and $\nu_{13} = (-\tfrac12 + \sigma i,\ \sigma_3 i,\ \tfrac12 + \sigma i)$, together with two families of $\mathbb{C}$-submodules $S, S' \colon \mathbb{N} \to \mathrm{Submodule}\,\mathbb{C}\,\mathbb{C}[X_0,X_1,X_2]$ such that the following holds, where the subtractions $\ell - 2$, $\ell - 1$ are truncated subtraction of natural numbers.
--
--   First, one of two parallel packages of thirteen conjuncts holds. The package for $\nu_{12}$ asserts, in this order: every $p \in S\,\ell$ is homogeneous of degree $\ell$ and harmonic, $\sum_i \partial_i^2 p = 0$; $S\,0 \le \mathbb{C}\cdot 1$; $S\,1 = \bot$; $S\,2 \le \mathbb{C}\langle X_0^2 - X_2^2,\ X_1^2 - X_2^2\rangle$; for every $\ell$ and $p \in S\,\ell$, $\mathrm{lower}_2(\Xi(\nu_{12},p)) \in S(\ell-2)$ and $\mathrm{lower}_1(\Xi(\nu_{12},p)) \in S(\ell-1)$; for every $p \in S\,2$, $\mathrm{same}_2(\Xi(\nu_{12},p)) \in S\,2$; $S\,0 = \bot$; every $p \in S'\,\ell$ is homogeneous of degree $\ell$ and harmonic; $S'\,0 = \bot$; $S'\,1 \le \mathbb{C}\cdot X_2$; $S'\,2 \le \mathbb{C}\cdot X_0X_1$; for every $\ell$ and $p \in S'\,\ell$, $\mathrm{lower}_2(\Xi(\nu_{12},p)) \in S'(\ell-2)$ and $\mathrm{lower}_1(\Xi(\nu_{12},p)) \in S'(\ell-1)$; and $S'\,1 = \bot$. The package for $\nu_{13}$ is the same list with $\nu_{12}$ replaced by $\nu_{13}$ throughout and with the two degree bounds on $S'$ replaced by $S'\,1 \le \mathbb{C}\cdot X_1$ and $S'\,2 \le \mathbb{C}\cdot X_0X_2$.
--
--   Second, and conjoined with that disjunction of packages: either $S\,\ell \ne \bot$ for some $\ell$, or $S'\,\ell \ne \bot$ for some $\ell$.
--
--   This is the analytic step, in the $\mathrm{GL}_3$ cubic-induction strand of the Langlands–Tunnell input, which confronts a Whittaker expansion whose exponents all have real part at least $1/2$ with the $K$-type bookkeeping at the boundary exponent $\operatorname{Re} e_{i_0} = 1/2$: either the coefficient functional $A$ vanishes identically on the module, or the spectral parameter is forced into one of the two shapes $\nu_{12}, \nu_{13}$ and is accompanied by graded families of harmonic polynomials, stable under the lowering operators attached to $\Xi$, satisfying the listed degree bounds and not all zero. It is used by [`LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate`](thm.html#LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate), where the second alternative is discarded and the vanishing of the critical-line coefficient is retained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re
    (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (hre : ∀ i : Fin m, 1 / 2 ≤ (e i).re)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hJ : 0 < J)
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2)
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (A : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h2 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M ∧
            ∀ (y₂ : ℝ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), A (fun g => w (g * k)) y₂ k' = A w y₂ (k' * k)))
    (h5 :
      (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h6 :
      (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        A (z • w₁ + w₂) y₂ k = z * A w₁ y₂ k + A w₂ y₂ k))
    (h7 :
      (∀ w ∈ M, ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, b i₀ j y₂ k = A w y₂ k) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ))
    (h8 :
      (∀ w ∈ M, ∀ i j : Fin 3, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => A w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))
          (A (WhittakerBlock.archDeriv i j w) y₂ k) 0))
    (h9 :
      (∀ w ∈ M, ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => A w y₂ (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))
          (A (WhittakerBlock.archDeriv c₂ c₁ w) y₂ k - A (WhittakerBlock.archDeriv c₁ c₂ w) y₂ k) 0))
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
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N)) :
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
    (∀ w ∈ M, ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, A w y₂ k = 0) ∨
    ∃ σ σ₃ : ℝ,
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I]
    ∃ S S' : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (((∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} ∧
          (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₂ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S (ℓ - 1)) ∧
          (∀ p ∈ S 2, same₂ (Ξ ν₁₂ p) ∈ S 2) ∧
          S 0 = ⊥ ∧
          (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S' ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S' 0 = ⊥ ∧
          S' 1 ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} ∧
          S' 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} ∧
          (∀ ℓ, ∀ p ∈ S' ℓ, lower₂ (Ξ ν₁₂ p) ∈ S' (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S' (ℓ - 1)) ∧
          S' 1 = ⊥) ∨
       ((∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} ∧
          (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₃ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S (ℓ - 1)) ∧
          (∀ p ∈ S 2, same₂ (Ξ ν₁₃ p) ∈ S 2) ∧
          S 0 = ⊥ ∧
          (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S' ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S' 0 = ⊥ ∧
          S' 1 ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} ∧
          S' 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} ∧
          (∀ ℓ, ∀ p ∈ S' ℓ, lower₂ (Ξ ν₁₃ p) ∈ S' (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S' (ℓ - 1)) ∧
          S' 1 = ⊥)) ∧
      ((∃ ℓ, S ℓ ≠ ⊥) ∨ (∃ ℓ, S' ℓ ≠ ⊥)) := by sorry
