-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule
-- name    : LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/119b127e-598a-55c5-838f-e75d05ada778
-- title:
--   Linear double-slot coefficient functional on a smoothing module
-- statement:
--   Fix a $\mathbb{C}$-submodule $M$ of the space of complex-valued functions on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$ (`AdelicGL 3 (𝓞 ℚ) ℚ`), and a homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^{\times}$. Throughout, $W_u$ denotes the Whittaker integral `whittaker3` of a function $u$, formed with the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` — so that the integration measure is the adelic additive Haar measure conditioned to the adelic box of $\mathbb{Q}$ — and with the standard global additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), i.e. $W_u(g)=\iiint u(n(x,y,z)g)\,\psi(-(x+y))$ over the upper unipotent matrices $n(x,y,z)$ of `upperUnipotent3`. Also, `WhittakerBlock.archDeriv c d φ` is the function $g\mapsto \frac{d}{ds}\varphi\bigl(g\cdot \mathrm{archRealLift3}(1+sE_{cd})\bigr)|_{s=0}$, `WhittakerBlock.casimir1`, `casimir2`, `casimir3` are the traces $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ of these operators, `IsArchSmooth3 φ` says that for every $g$ the map $e\mapsto \varphi(g\cdot \mathrm{archRealLift3}\,e)$ is smooth on the locus of invertible real $3\times 3$ matrices, `orth3` is the set of $k$ with $k^{\mathsf T}k=1$ over the infinite adeles, and `gauge3` is the archimedean-times-finite size function $\max(1,\mathrm{archGauge3}\cdot\mathrm{finGauge3})$.
--
--   The hypotheses on $M$ are: `h1`, that every $w\in M$ is archimedean-smooth, has archimedean-smooth Whittaker integral $W_w$, has all iterated `archDeriv` words continuous, and is left invariant under the rational points $\mathrm{GL}_3(\mathbb{Q})$ embedded via `globalPointsGL`; `h3`, that each $w\in M$ admits a finite set $s$ of functions such that for every adelic $k$ whose component at each height-one prime is $1$ and whose archimedean component lies in `orth3`, the translate $g\mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$; `h4`, that $M$ is stable under these translates; `h5`, that $M$ is stable under every `archDeriv i j`; `h10`, the existence of a form $B$ on functions which on $M$ is Hermitian, linear in its first argument, has $\mathrm{Re}\,B(w,w)>0$ for $0\neq w\in M$, satisfies $B(\partial_{ij}w,w')=-B(w,\partial_{ij}w')$, and is invariant under the above translates; `h11`, the existence of monic polynomial relations of degrees $N_1,N_2,N_3$ annihilating `casimir1`, `casimir2`, `casimir3` on $M$; `h12`, that every $v\in M$ transforms under the central idelic scalars `centralScalarGL` by the character $\omega$; and `h13`, that each $v\in M$ has an exponent $N$ such that every iterated `archDeriv` word applied to $v$ is bounded by a constant times $\mathrm{gauge3}(g)^{N}$.
--
--   In addition, monic coefficient families $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ and $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ (with value $1$ at the last index) are fixed, together with the hypothesis `hrel` that every $w\in M$ satisfies the two relations $\sum_l a_2(l)\,\mathrm{casimir2}^{[l]}w=0$ and $\sum_l a_3(l)\,\mathrm{casimir3}^{[l]}w=0$. Expansion data are fixed as well: a real $\rho$, naturals $n$ and $J$, an injective family of exponents $e : \mathrm{Fin}\,n\to\mathbb{C}$ with $\mathrm{Re}\,e(i)\le\rho$ for all $i$, and $\delta>0$.
--
--   The hypothesis `hexp` is the joint-expansion input, stated verbatim for an arbitrary exponent $N$ and an arbitrary function $u$ on $\mathrm{GL}_3$ of the adeles: if $u$ has all `archDeriv` words continuous, is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, transforms under the central idelic scalars by $\omega$, is archimedean-smooth, has all its orthogonal translates in the span of a single finite set, satisfies the two monic Casimir relations with $a_2$ and $a_3$, and has all `archDeriv` words bounded by a constant times $\mathrm{gauge3}^{N}$, then $W_u$ admits both of the two joint expansions along the torus element $\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)$. In the first, there are coefficients $c_{ij}(y_2,k)$, jointly continuous on $\{y_2>0\}$, such that for every compact $K$ and every $b\ge 1$ there is a $C$ with
--   $$\Bigl\|W_u\bigl(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\bigr)-\sum_{i,j}c_{ij}(y_2,k)\,y_1^{e(i)}(\log y_1)^{j}\Bigr\|\le C\,y_1^{\rho+\delta}$$
--   for $k\in K$, $b^{-1}\le y_2\le b$ and $0<y_1\le 1$; there are continuous second-layer coefficients $c'_{iji'j'}(k)$ with $\|c_{ij}(y_2,k)-\sum_{i',j'}c'_{iji'j'}(k)\,y_2^{e(i')}(\log y_2)^{j'}\|\le C\,y_2^{\rho+\delta}$ uniformly for $k$ in compacta and $0<y_2\le1$; and a cascade clause: for each $(i,j)$, if $c_{i''j''}$ vanishes identically for all $(i'',j'')$ with $\mathrm{Re}\,e(i'')<\mathrm{Re}\,e(i)$ and all $c'_{iji'j'}$ vanish identically, then $c_{ij}(y_2,k)=0$ for all $k$ and all $y_2>0$. The second expansion is the same statement with the roles of $y_1$ and $y_2$ interchanged. Finally, indices $i_9,i_9'\in\mathrm{Fin}\,n$ and $j_0,j_0'\in\mathrm{Fin}\,J$ are fixed.
--
--   Under these hypotheses there exists a $\mathbb{C}$-linear map $\Lambda : M \to (\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C})$ with the following three properties.
--
--   First, $\Lambda$ reads off the prescribed second-layer coefficient: for every $v\in M$ and every pair of families $(c^v, c^{v\prime})$ satisfying the four-clause joint-expansion block for $v$ in the $y_1$-direction — joint continuity of $c^v_{ij}$ on $\{y_2>0\}$, the approximation bound for $W_v$ along $\mathrm{diag}(y_1y_2,y_2,1)\cdot k$ with error $C y_1^{\rho+\delta}$ uniformly for $k$ compact and $y_2$ in $[b^{-1},b]$, continuity of each $c^{v\prime}_{iji'j'}$, and the second-layer bound with error $C y_2^{\rho+\delta}$ — one has $\Lambda(v)(k)=c^{v\prime}_{i_9 j_0 i_9' j_0'}(k)$ for every $k$.
--
--   Second, $\Lambda$ is equivariant for right translation by the relevant group elements: for $v\in M$ and every $k'$ whose component at each height-one prime is $1$ and whose archimedean component lies in `orth3`, the translate $x\mapsto v(xk')$ lies in $M$ (by `h4`) and $\Lambda$ of it, evaluated at $g$, equals $\Lambda(v)(gk')$.
--
--   Third, $\Lambda$ intertwines the archimedean derivatives: for $v\in M$, indices $c,d\in\mathrm{Fin}\,3$ and every $g$, the function $s\mapsto \Lambda(v)\bigl(g\cdot\mathrm{archRealLift3}(1+sE_{cd})\bigr)$ is differentiable at $s=0$ with derivative $\Lambda(\mathrm{archDeriv}\ c\ d\ v)(g)$, the argument lying in $M$ by `h5`.
--
--   This packages the passage from a smoothing module of automorphic functions on $\mathrm{GL}_3$ over $\mathbb{Q}$ to a single linear functional-valued map extracting one coefficient of the iterated $y^{e}(\log y)^{j}$ expansion of the Whittaker integral along the diagonal torus, together with its compatibility with orthogonal right translation and with the Lie-algebra action. It is used in the vanishing arguments for homogeneous and sign-isotypic pieces of the induced picture, where the extracted coefficient is shown to vanish identically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule
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
    (i9 i9' : Fin n) (j₀ j₀' : Fin J) :
    ∃ Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
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
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ k = cv' i9 j₀ i9' j₀' k) ∧
      (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k')) ∧
      (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0) := by sorry
