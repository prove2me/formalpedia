-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_signProjection_read_kernel_stable_of_doubleSlotCoeffMap
-- name    : LanglandsTunnell.CubicInduction.signProjection_read_kernel_stable_of_doubleSlotCoeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8bef55a7-2fe3-5bbd-b087-6687ae69f3e7
-- title:
--   Kernel of the sign-projected read is translation- and derivative-stable
-- statement:
--   Throughout, $G$ denotes `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group $\mathrm{GL}_3$ over the adele ring of $\mathbb{Q}$, and attention is restricted to functions $G \to \mathbb{C}$. Three pieces of notation recur. For a real $3 \times 3$ matrix $e$, [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) is the element of $G$ determined by $e$ at the archimedean place when $e$ is invertible, and $1$ otherwise; `WhittakerBlock.archDeriv i j φ` is the function $g \mapsto \frac{d}{ds}\big|_{s=0} φ\big(g \cdot \mathrm{archRealLift3}(1 + s E_{ij})\big)$, and `casimir2`, `casimir3` are the associated sums $\sum_{i,j} \partial_{ij}\partial_{ji}$ and $\sum_{i,j,k} \partial_{ij}\partial_{jk}\partial_{ki}$; `orth3` is the set of $k \in \mathrm{GL}_3(\text{infinite adeles of } \mathbb{Q})$ with $k^{\mathsf T} k = 1$. Finally `whittaker3 P ψ Φ g` is the iterated integral $\int\!\!\int\!\!\int Φ(u_3(x,y,z)\, g)\, ψ(-(x+y))$ over the upper unipotent coordinates, taken with respect to the measure attached to the pins $P$; here $P$ is `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, whose measure is the adelic additive Haar measure conditioned on the adelic box (infinite box times integral finite adeles), and $ψ$ is the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615).
--
--   The data are a $\mathbb{C}$-subspace $M$ of functions $G \to \mathbb{C}$ and a homomorphism $ω$ from the ideles $(\mathbb{A}_{\mathbb{Q}})^\times$ to $\mathbb{C}^\times$, subject to the following groups of hypotheses on $M$. `h1` (regularity and automorphy): every $w \in M$ is archimedean-smooth in the sense of [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) (for each $g$ the map $e \mapsto w(g \cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det e \ne 0\}$), its Whittaker integral `whittaker3 P ψ w` is likewise archimedean-smooth, every iterated `archDeriv` of $w$ along a finite list of index pairs is continuous, and $w$ is left invariant under the global points `globalPointsGL 3 (𝓞 ℚ) ℚ γ`, $γ \in \mathrm{GL}_3(\mathbb{Q})$. `h3` (finiteness of right translates): for each $w \in M$ there is a finite set $s$ of functions such that $g \mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$ for every $k$ with `componentAt3` trivial at every height-one prime and `archComponent3` in `orth3`. `h4` and `h5` (stability): $M$ is stable under such right translations and under the nine operators `archDeriv i j`. `h10` (inner product): there is a form $B$ on functions such that on $M$ it is conjugate-symmetric, linear in its first argument, satisfies $0 < \mathrm{Re}\,B(w,w)$ for $w \ne 0$, makes each `archDeriv i j` skew-adjoint, and is invariant under right translation by the $k$ just described. `h11` (Casimir relations): there are monic coefficient vectors $a_1, a_2, a_3$ of lengths $N_1+1, N_2+1, N_3+1$ (value $1$ at `Fin.last`) with $\sum_l a_m(l)\,\mathrm{casimir}m^{[l]}w = 0$ for all $w \in M$ and $m = 1,2,3$. `h12` (central character): $v(\mathrm{centralScalarGL}(z)\,g) = ω(z)\,v(g)$ for $v \in M$. `h13` (moderate growth): for each $v \in M$ there is $N$ such that every iterated `archDeriv` of $v$ along a list is bounded by $C\,\mathrm{gauge3}(g)^N$, where $\mathrm{gauge3}(g) = \max(1, \mathrm{archGauge3}(g)\,\mathrm{finGauge3}(g))$.
--
--   Further data: naturals $N_2, N_3$ with coefficient vectors $a_2, a_3$ taking the value $1$ at `Fin.last` (`ha₂`, `ha₃`), and `hrel`, which asserts that every $w \in M$ is annihilated by the corresponding polynomials in `casimir2` and in `casimir3`; a real $ρ$, naturals $n, J$, an injective $e : \mathrm{Fin}\,n \to \mathbb{C}$ (`he`) with $\mathrm{Re}(e_i) \le ρ$ for all $i$ (`hre`), and a real $δ > 0$.
--
--   The hypothesis `hexp` is a two-variable asymptotic expansion axiom. For every $N$ and every function $u$ on $G$ satisfying: continuity of all iterated `archDeriv`s, left invariance under $\mathrm{GL}_3(\mathbb{Q})$, the central character condition for $ω$, archimedean smoothness, the finite-span property for right translates by $k$ trivial at the finite places and orthogonal at infinity, annihilation by the $a_2$-polynomial in `casimir2` and by the $a_3$-polynomial in `casimir3`, and the bound $C\,\mathrm{gauge3}(g)^N$ for all iterated `archDeriv`s, both of the following hold. First, there are coefficients $c_{ij}(y,k)$ ($i \in \mathrm{Fin}\,n$, $j \in \mathrm{Fin}\,J$), continuous on $\{(y,k) : y > 0\}$, such that for every compact $K \subseteq G$ and every $b \ge 1$ there is $C$ with
--   $$\Big\| W_u\big(\mathrm{archRealLift3}(\mathrm{diag}(y_1y_2, y_2, 1))\cdot k\big) - \sum_{i,j} c_{ij}(y_2,k)\, y_1^{e_i} (\log y_1)^j \Big\| \le C\, y_1^{ρ+δ}$$
--   for $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$, where $W_u = \mathrm{whittaker3}\,P\,ψ\,u$; and there are further coefficients $c'_{iji'j'}(k)$, continuous in $k$, such that for every compact $K$ there is $C$ with $\|c_{ij}(y_2,k) - \sum_{i',j'} c'_{iji'j'}(k)\, y_2^{e_{i'}}(\log y_2)^{j'}\| \le C\,y_2^{ρ+δ}$ for $k \in K$, all $i,j$ and $0 < y_2 \le 1$; together with the vanishing clause: for each $(i,j)$, if $c_{i''j''}(y_2,k) = 0$ for all $k$, all $y_2 > 0$ and all $(i'',j'')$ with $\mathrm{Re}(e_{i''}) < \mathrm{Re}(e_i)$, and if $c'_{iji'j'}$ vanishes identically for all $(i',j')$, then $c_{ij}(y_2,k) = 0$ for all $k$ and all $y_2 > 0$. Second, the same statement with the roles of $y_1$ and $y_2$ interchanged (leading expansion in $y_2$ with coefficients depending on $y_1$, secondary expansion of those coefficients in $y_1$, and the corresponding vanishing clause).
--
--   Finally there are indices $i_9, i_9' \in \mathrm{Fin}\,n$ and $j_0, j_0' \in \mathrm{Fin}\,J$, a vector $ν : \mathrm{Fin}\,3 \to \mathbb{C}$, and a $\mathbb{C}$-linear map $Λ$ from $M$ to functions on $G$, with three hypotheses. `hΛa` (double-slot read): for every $v \in M$ and every pair of families $c_v, c_v'$ satisfying the four clauses of the first expansion above for $v$ (continuity on $\{y > 0\}$, the $y_1$-expansion uniform for $y_2$ in compact intervals and $k$ in compact sets, continuity of $c_v'$, and the secondary $y_2$-expansion of $c_v$), one has $Λ(v)(k) = c'_{v,\,i_9 j_0 i_9' j_0'}(k)$ for all $k$. `hΛb` (equivariance for translations): $Λ(g \mapsto v(gk'))(g) = Λ(v)(gk')$ whenever $k'$ is trivial at every finite place and orthogonal at infinity. `hΛc` (intertwining the nine flows): for $v \in M$ and $c,d \in \mathrm{Fin}\,3$, the map $s \mapsto Λ(v)\big(g \cdot \mathrm{archRealLift3}(1 + s E_{cd})\big)$ has derivative $Λ(\mathrm{archDeriv}\,c\,d\,v)(g)$ at $s = 0$.
--
--   The remaining data are a sign vector $ε : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$, an element $k_1 \in G$ with trivial archimedean component, and a subspace $H \le M$ (`hle`) which is stable under right translation by $k$ trivial at the finite places and orthogonal at infinity (`hHK`) and under the nine `archDeriv i j` (`hHD`), and on which $Λ$ is equivariant for the positive upper-triangular group (`hHeq`): for $u \in H$, every $t$ with $t_{ij} = 0$ for $j < i$ and $t_{ii} > 0$, and every $g$,
--   $$Λ(u)\big(\mathrm{archRealLift3}(t)\cdot g\big) = \Big(\prod_{a} t_{aa}^{\,ν_a + (1,0,-1)_a}\Big)\, Λ(u)(g).$$
--   Let $u \in H$, and assume `hker`: for every real $3\times3$ matrix $o$ with $\sum_a o_{ai}o_{aj} = δ_{ij}$,
--   $$\tfrac18 \sum_{τ : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2} (-1)^{\sum_a ε_a τ_a}\, Λ(u)\Big(\mathrm{archRealLift3}\big(\mathrm{diag}((-1)^{τ_a})\big)\cdot\big(\mathrm{archRealLift3}(o)\cdot k_1\big)\Big) = 0 .$$
--
--   The conclusion is the conjunction of two statements. First: for every $k \in G$ with `componentAt3` trivial at every height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and `archComponent3` in `orth3`, and for every real $o$ with $\sum_a o_{ai}o_{aj} = δ_{ij}$, the same sign-projected sum vanishes for the translate $g \mapsto u(gk)$ (an element of $H$ by `hHK`, hence of $M$), that is,
--   $$\tfrac18 \sum_{τ} (-1)^{\sum_a ε_a τ_a}\, Λ\big(g \mapsto u(gk)\big)\Big(\mathrm{archRealLift3}\big(\mathrm{diag}((-1)^{τ_a})\big)\cdot\big(\mathrm{archRealLift3}(o)\cdot k_1\big)\Big) = 0 .$$
--   Second: for all $c, d \in \mathrm{Fin}\,3$ and every real $o$ with $\sum_a o_{ai}o_{aj} = δ_{ij}$, the same sign-projected sum vanishes for $\mathrm{archDeriv}\,c\,d\,u$ (an element of $H$ by `hHD`, hence of $M$).
--
--   This is the stability step showing that the vanishing locus of the $ε$-sign projection of the double-slot coefficient read $Λ$, evaluated along the orthogonal orbit through $k_1$, is a subspace closed under right translation by the relevant compact elements and under the nine archimedean derivative operators. It is used by [`LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule), and it invokes the Iwasawa-type factorisation [`Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero`](thm.html#Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero) together with the equivariance and sign-isotypy of the projection recorded in [`LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection`](thm.html#LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_signProjection_read_kernel_stable_of_doubleSlotCoeffMap.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.signProjection_read_kernel_stable_of_doubleSlotCoeffMap
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
    (H : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hle : H ≤ M)
    (hHK : (∀ w ∈ H, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ H))
    (hHD : (∀ w ∈ H, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H))
    (hHeq : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ H), (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hle hu⟩ g))
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ H)
    (hker : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) :
    (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
        (hk2 : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
        ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨fun g => u (g * k), hle (hHK u hu k hk1 hk2)⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) ∧
    (∀ (c d : Fin 3), ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨WhittakerBlock.archDeriv c d u, hle (hHD u hu c d)⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) := by sorry
