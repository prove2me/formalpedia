-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_polynomialModel_positive_actSkew_form_of_separating_stable_submodule
-- name    : LanglandsTunnell.CubicInduction.exists_polynomialModel_positive_actSkew_form_of_separating_stable_submodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/8db2d7bb-d23e-5646-8d96-1f4b44fcfe8a
-- title:
--   Polynomial model for a separating stable submodule
-- statement:
--   Throughout, $G=\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ is `AdelicGL 3 (𝓞 ℚ) ℚ`, and functions on $G$ are complex valued. For a real $3\times 3$ matrix $e$, [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) denotes the element of $G$ obtained from $e$ when the associated archimedean matrix is a unit (and $1$ otherwise); `WhittakerBlock.archDeriv i j φ` is the derivative at $s=0$ of $s\mapsto φ(g\cdot\mathrm{archRealLift3}(1+sE_{ij}))$, and `WhittakerBlock.casimir1`, `casimir2`, `casimir3` are the operators $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ built from these nine derivations. [`WhittakerBlock.IsArchSmooth3 φ`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) says that for every $g$ the map $e\mapsto φ(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det e\neq 0\}$. `orth3` is the set of $k\in\mathrm{GL}_3$ of the infinite adeles with $k^{\mathsf T}k=1$; `gauge3 ℚ g` is $\max(1,\text{archimedean gauge}\cdot\text{finite gauge})$; and `whittaker3` is the threefold integral of $Φ(u_3(x,y,z)g)\,ψ(-(x+y))$ against the measure attached to the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` (adelic Haar measure conditioned on the adelic box), with $ψ$ the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615).
--
--   The data are: a $\mathbb{C}$-submodule $M$ of functions on $G$; a character $ω$ of the idele class group to $\mathbb{C}^\times$; and eight hypotheses on $M$. `h1`: every $w\in M$ is arch-smooth, its `whittaker3` transform is arch-smooth, every iterated archimedean derivative of $w$ along a finite word of index positions is continuous, and $w$ is left invariant under the global points $\mathrm{GL}_3(\mathbb{Q})$. `h3`: each $w\in M$ is $K$-finite, i.e. there is a finite set $s$ of functions such that for all $k$ trivial at every finite place with archimedean component in `orth3` the translate $g\mapsto w(gk)$ lies in the span of $s$. `h4`: $M$ is stable under such translations. `h5`: $M$ is stable under all nine `archDeriv`. `h10`: there exists a form $B$ on functions which, on $M$, is Hermitian, linear in its first argument, positive ($0<\mathrm{Re}\,B(w,w)$ for $0\neq w\in M$), makes each `archDeriv` skew, and is invariant under the above translations. `h11`: there exist monic one-variable relations (coefficient families $a_1,a_2,a_3$ with last coefficient $1$) annihilating every $w\in M$ for each of `casimir1`, `casimir2`, `casimir3`. `h12`: every $v\in M$ has central character $ω$. `h13`: every $v\in M$ has moderate growth, with a single exponent $N$ and a constant depending on the differentiation word, measured by `gauge3`.
--
--   Further data: explicit monic relations $N_2,a_2$ and $N_3,a_3$ (last coefficients $1$) with `hrel` asserting that they annihilate `casimir2` and `casimir3` on all of $M$; a real exponent $ρ$, naturals $n,J$, an injective family $e:\mathrm{Fin}\,n\to\mathbb{C}$ with $\mathrm{Re}(e_i)\le ρ$, and $δ>0$.
--
--   The hypothesis `hexp` is the asymptotic expansion input: for every $N$ and every function $u$ on $G$ whose iterated archimedean derivatives are continuous, which is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, has central character $ω$, is arch-smooth, is $K$-finite in the sense of `h3`, satisfies the two monic Casimir relations given by $a_2$ and $a_3$, and satisfies the growth bound with exponent $N$, two expansions of the Whittaker function of $u$ along the torus points $\mathrm{archRealLift3}(\mathrm{diag}(y_1y_2,y_2,1))\cdot k$ are asserted, one in $y_1\to 0$ with coefficients $c_{ij}(y_2,k)$ and one in $y_2\to 0$ with coefficients $c_{ij}(y_1,k)$. Each of the two branches (summarised here; the two are symmetric in the roles of $y_1$ and $y_2$) consists of four clauses: joint continuity of the coefficients on $\{$first variable $>0\}$; the leading estimate, in which the Whittaker function minus $\sum_{i,j} c_{ij}\,y^{e_i}(\log y)^{j}$ is $O(y^{ρ+δ})$ uniformly for $k$ in a compact set and the other torus variable in $[b^{-1},b]$; the existence of continuous secondary coefficients $c'_{iji'j'}$ with $c_{ij}-\sum_{i',j'}c'_{iji'j'}\,y^{e_{i'}}(\log y)^{j'}=O(y^{ρ+δ})$ uniformly on compacta; and a cascade clause: if all $c_{i''j''}$ with $\mathrm{Re}(e_{i''})<\mathrm{Re}(e_i)$ vanish identically and all $c'_{ij\,\cdot\,\cdot}$ vanish, then $c_{ij}$ vanishes.
--
--   Finally there are indices $i_9,i_9'\in\mathrm{Fin}\,n$, $j_0,j_0'\in\mathrm{Fin}\,J$, a family $ν:\mathrm{Fin}\,3\to\mathbb{C}$, and a $\mathbb{C}$-linear map $Λ:M\to(G\to\mathbb{C})$ subject to three conditions. `hΛa`: for every $v\in M$ and any two families $c_v,c_v'$ satisfying the four clauses of the $y_1$-first branch for $v$, one has $Λ(v)=c_v'(i_9,j_0,i_9',j_0')$ pointwise, so $Λ$ reads off a fixed secondary coefficient. `hΛb`: $Λ$ commutes with right translation by any $k'$ trivial at all finite places with archimedean component in `orth3`. `hΛc`: $Λ$ intertwines the nine flows, namely $s\mapsto Λ(v)(g\cdot\mathrm{archRealLift3}(1+sE_{cd}))$ has derivative $Λ(\mathrm{archDeriv}\,c\,d\,v)(g)$ at $s=0$.
--
--   The last data are a sign vector $ε:\mathrm{Fin}\,3\to\mathrm{Fin}\,2$, an element $k_1\in G$ with trivial archimedean component, and a submodule $M'\le M$ such that `hK`: $M'$ is stable under the translations of `h4`; `hD`: $M'$ is stable under the nine `archDeriv`; `hEq`: for every $u\in M'$ the function $Λ(u)$ is equivariant for upper triangular real matrices $t$ with positive diagonal, $Λ(u)(\mathrm{archRealLift3}\,t\cdot g)=\bigl(\prod_a t_{aa}^{\,ν_a+(1,0,-1)_a}\bigr)Λ(u)(g)$; and `hsep`: $M'$ is separated by the $ε$-sign projection of $Λ$ on the orthogonal orbit, i.e. if for every real $o$ with $\sum_a o_{a,i}o_{a,j}=δ_{ij}$ the quantity $\frac18\sum_{τ}(-1)^{\sum_a ε_aτ_a}Λ(u)\bigl(\mathrm{archRealLift3}(\mathrm{diag}((-1)^{τ_a}))\cdot(\mathrm{archRealLift3}\,o\cdot k_1)\bigr)$ vanishes, then $u=0$.
--
--   Let `act` be the operator on $\mathbb{C}[X_{(a,b)}:(a,b)\in\mathrm{Fin}\,3\times\mathrm{Fin}\,3]$ given, for $ν$ and indices $c,d$, by
--   $$\mathrm{act}\,ν\,c\,d\,(p)=\Bigl(\sum_a C(ν_a+(1,0,-1)_a)X_{(a,c)}X_{(a,d)}\Bigr)p+\sum_{i,j}\Bigl(\sum_m \theta_{i,m}^{c,d}\,X_{(m,j)}\Bigr)\,\partial_{(i,j)}p,$$
--   where $\theta_{i,m}^{c,d}=X_{(i,c)}X_{(m,d)}$ if $m<i$, $-X_{(m,c)}X_{(i,d)}$ if $i<m$, and $0$ if $m=i$.
--
--   The conclusion asserts the existence of a $\mathbb{C}$-submodule $W$ of $\mathbb{C}[X_{(a,b)}]$ and a function $β$ of two polynomials with values in $\mathbb{C}$ such that: (i) $W$ is stable under every $\mathrm{act}\,ν\,c\,d$; (ii) $W$ is stable under right rotation, i.e. under the substitution $X_{(i,j)}\mapsto\sum_c X_{(i,c)}C(r_{c,j})$ for every real $r$ with $\sum_a r_{a,i}r_{a,j}=δ_{ij}$; (iii) every $P\in W$ is $ε$-sign isotypic: for every $τ:\mathrm{Fin}\,3\to\mathrm{Fin}\,2$ and every orthogonal $o$, the evaluation of $P$ at the entries of $\mathrm{diag}((-1)^{τ_a})\cdot o$ equals $(-1)^{\sum_a ε_aτ_a}$ times its evaluation at the entries of $o$; (iv) $β$ is linear in its first argument on $W$; (v) $β$ is Hermitian on $W$, $β(Q,P)=\overline{β(P,Q)}$; (vi) if $P\in W$ evaluates to $0$ at every orthogonal matrix, then $β(P,Q)=0$ for all $Q\in W$; (vii) if $P\in W$ has nonzero evaluation at some orthogonal matrix, then $0<\mathrm{Re}\,β(P,P)$; (viii) $β$ is invariant under applying the right rotation substitution by an orthogonal $r$ to both arguments; (ix) $β$ is `act`-skew: $β(\mathrm{act}\,ν\,c\,d\,P,Q)=-β(P,\mathrm{act}\,ν\,c\,d\,Q)$ for $P,Q\in W$ and all $c,d$; and (x) every $u\in M'$ is represented in $W$: there is $P\in W$ whose evaluation at the entries of any orthogonal $o$ equals the $ε$-sign projection $\frac18\sum_{τ}(-1)^{\sum_a ε_aτ_a}Λ(u)\bigl(\mathrm{archRealLift3}(\mathrm{diag}((-1)^{τ_a}))\cdot(\mathrm{archRealLift3}\,o\cdot k_1)\bigr)$.
--
--   This is the transport step from the adelic picture to a finite-dimensional polynomial model: the $ε$-sign projected archimedean reads of the coefficient functional $Λ$ on a separating, translation- and derivative-stable subspace $M'$ are realised as polynomial functions in the nine entries of an orthogonal matrix, carrying across the stability under the nine flows (in the form of the operator `act`), the rotation action, the sign isotypy, and the positive, `act`-skew invariant form inherited from $B$. It supplies the hypotheses of the sign-parity vanishing statement and is used by [`LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package`](thm.html#LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package) in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_polynomialModel_positive_actSkew_form_of_separating_stable_submodule.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_polynomialModel_positive_actSkew_form_of_separating_stable_submodule
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
    (i9 i9' : Fin n) (j₀ j₀' : Fin J) (ν : Fin 3 → ℂ)
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
    :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    ∃ (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
      (β : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → ℂ),
      (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) ∧
      (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) ∧
      (∀ P ∈ W, ∀ τ : Fin 3 → Fin 2, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => (((∑ c : Fin 3, (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) ij.1 c * o c ij.2) : ℝ) : ℂ)) P =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) ∧
      (∀ (z : ℂ), ∀ P₁ ∈ W, ∀ P₂ ∈ W, ∀ Q ∈ W, β (z • P₁ + P₂) Q = z * β P₁ Q + β P₂ Q) ∧
      (∀ P ∈ W, ∀ Q ∈ W, β Q P = (starRingEnd ℂ) (β P Q)) ∧
      (∀ P ∈ W, (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) → ∀ Q ∈ W, β P Q = 0) ∧
      (∀ P ∈ W, (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → 0 < (β P P).re) ∧
      (∀ P ∈ W, ∀ Q ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        β (MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P)
          (MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) Q) = β P Q) ∧
      (∀ P ∈ W, ∀ Q ∈ W, ∀ c d : Fin 3, β (act ν c d P) Q = -β P (act ν c d Q)) ∧
      (∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'), ∃ P ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P =
          ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁)))) := by sorry
