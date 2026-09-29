-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
-- name    : LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/7823f7a6-88ca-5c0f-9448-20b5c990d812
-- title:
--   Admissibility of the cyclic hull at a fixed type
-- statement:
--   Throughout, functions are complex-valued functions on the adelic group $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, written `AdelicGL 3 (𝓞 ℚ) ℚ`, and the operators $\partial_{ij} =$ `WhittakerBlock.archDeriv i j` are the archimedean right derivatives $(\partial_{ij}\varphi)(g) = \frac{d}{ds}\varphi\bigl(g\cdot \mathrm{archRealLift3}(I + s\,E_{ij})\bigr)\big|_{s=0}$; `casimir1`, `casimir2`, `casimir3` are the traces $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ of these. The set `orth3` consists of those $k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ with $k^{\mathsf{T}}k = 1$; `gauge3` is $\max(1, \mathrm{archGauge3}\cdot\mathrm{finGauge3})$; and `whittaker3` is the threefold integral $\int\!\!\int\!\!\int \Phi(u_3(x,y,z)g)\,\psi(-(x+y))$ against the measure attached to the given pin data, here `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` (whose relevant ingredient is the adelic additive Haar measure conditioned on the standard adelic box) and the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615).
--
--   The data are a $\mathbb{C}$-submodule $M$ of the space of such functions and a character $\omega$ of the idele units, i.e. a monoid homomorphism $(\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$, subject to the following groups of hypotheses on $M$.
--
--   `h1` (smoothness and automorphy): every $w \in M$ satisfies `IsArchSmooth3`, that is, for each $g$ the map $e \mapsto w(g\cdot\mathrm{archRealLift3}\,e)$ is $C^{\infty}$ on the set of real $3\times 3$ matrices of nonzero determinant; the Whittaker integral of $w$ is again `IsArchSmooth3`; every iterated derivative $\partial_{i_1j_1}\cdots\partial_{i_rj_r}w$ indexed by a list of pairs is continuous; and $w(\gamma g) = w(g)$ for all $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, embedded by `globalPointsGL`.
--
--   `h3` ($O(3)$-finiteness): for each $w \in M$ there is a finite set $s$ of functions such that for every $k$ whose component at each finite place is $1$ and whose archimedean component lies in `orth3`, the right translate $g \mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$.
--
--   `h4` (stability under orthogonal translation) and `h5` (stability under the nine derivatives): for $w \in M$ and $k$ as in `h3`, $g\mapsto w(gk)$ lies in $M$; and $\partial_{ij}w \in M$ for all $i,j$.
--
--   `h10` (positive form): there exists $B$ on pairs of functions which, on members of $M$, is conjugate-symmetric, linear in its first argument, satisfies $\mathrm{Re}\,B(w,w) > 0$ for $w \neq 0$, is skew for each $\partial_{ij}$, and is invariant under the right translations of `h3`.
--
--   `h11` (central relations): there are monic polynomial relations, of degrees $N_1, N_2, N_3$ and with coefficient families $a_1, a_2, a_3$ whose top coefficients are $1$, annihilating every $w \in M$ when applied to the iterates of `casimir1`, `casimir2`, `casimir3` respectively.
--
--   `h12` (central character): $v(z\cdot g) = \omega(z)\,v(g)$ for $v \in M$, $z$ an idele unit acting through `centralScalarGL`, and all $g$.
--
--   `h13` (moderate growth): for $v \in M$ there is $N$ such that each iterated derivative word applied to $v$ is bounded by $C\,\mathrm{gauge3}(g)^{N}$ for some constant depending on the word.
--
--   In addition, explicit data $N_2$, $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ with $a_2(N_2) = 1$, and $N_3$, $a_3$ with $a_3(N_3) = 1$ are given, together with `hrel`: the two corresponding monic relations in `casimir2` and in `casimir3` annihilate every $w \in M$.
--
--   Asymptotic data: a real $\rho$, naturals $n, J$, an injective family $e : \mathrm{Fin}\,n \to \mathbb{C}$ of exponents with $\mathrm{Re}\,e_i \le \rho$ for all $i$, and $\delta > 0$. The hypothesis `hexp` asserts an expansion principle: for every natural $N$ and every function $u$ which has continuous derivative words, is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, transforms by $\omega$ under the adelic centre, is `IsArchSmooth3`, is $O(3)$-finite in the sense of `h3`, is annihilated by the two monic relations with coefficients $a_2$ and $a_3$, and whose derivative words are bounded by $C\,\mathrm{gauge3}(g)^{N}$, two conclusions hold simultaneously. The first provides coefficients $c : \mathrm{Fin}\,n \to \mathrm{Fin}\,J \to \mathbb{R} \to (\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C})$, jointly continuous on $\{p : 0 < p_1\}$, such that for every compact $K$ and every $b \ge 1$ there is $C$ with
--   $$\Bigl\|\,\mathrm{whittaker3}(u)\bigl(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2, y_2, 1)\cdot k\bigr) - \sum_{i,j} c_{ij}(y_2, k)\, y_1^{e_i}(\log y_1)^{j}\Bigr\| \le C\,y_1^{\rho+\delta}$$
--   for $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$; together with secondary coefficients $c'$, indexed by two pairs and continuous, satisfying on each compact $K$ an analogous estimate $\bigl\|c_{ij}(y_2,k) - \sum_{i',j'} c'_{iji'j'}(k)\,y_2^{e_{i'}}(\log y_2)^{j'}\bigr\| \le C\,y_2^{\rho+\delta}$ for $0 < y_2 \le 1$, and a vanishing clause: for each $(i,j)$, if $c_{i''j''}$ vanishes identically (for all $k$ and all $y_2 > 0$) for every $i''$ with $\mathrm{Re}\,e_{i''} < \mathrm{Re}\,e_i$, and if all $c'_{iji'j'}$ vanish, then $c_{ij}(y_2,k) = 0$ for all $k$ and all $y_2 > 0$. The second conclusion is the statement obtained by interchanging the roles of $y_1$ and $y_2$ throughout: expansion of the same Whittaker value in powers $y_2^{e_i}(\log y_2)^{j}$ with coefficients depending on $y_1$, error $C\,y_2^{\rho+\delta}$ for $b^{-1}\le y_1 \le b$, secondary expansion of those coefficients in $y_1$, and the corresponding vanishing clause.
--
--   Finally, naturals $a$ and $\ell$ are given with $a \in \{0,1\}$ (`ha`) and $\ell \in \{0,1\}$ (`hℓ`); the number $a$ occurs nowhere else in the statement. A function $f \in M$ is given which is of type $\tau$ in the following sense (`hfτ`): either $\ell = 0$ and $\partial_{ij}f - \partial_{ji}f = 0$ for all $i,j$, or $\ell = 1$ and
--   $$\bigl(\partial_{01}-\partial_{10}\bigr)^2 f + \bigl(\partial_{02}-\partial_{20}\bigr)^2 f + \bigl(\partial_{12}-\partial_{21}\bigr)^2 f + 2f = 0,$$
--   the squares being written out as the indicated differences of composites. Lastly, $H$ is a submodule with $H \le M$ (`hHM`) and $f \in H$ (`hfH`), closed under the right translations by $k$ as in `h3` (`hHK`) and under the nine derivatives $\partial_{ij}$ (`hHD`), and minimal with these properties (`hHmin`): any submodule $H' \le M$ containing $f$ and closed under those translations and derivatives satisfies $H \le H'$.
--
--   The conclusion is that there exists a submodule $E$ of the space of complex-valued functions on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that $E$ is finite-dimensional over $\mathbb{C}$, and every $u \in H$ which is of type $\tau$ — that is, which satisfies the same disjunction as $f$, with $u$ in place of $f$: either $\ell = 0$ and $\partial_{ij}u - \partial_{ji}u = 0$ for all $i,j$, or $\ell = 1$ and the above rotation Casimir plus $2$ annihilates $u$ — belongs to $E$. No containment of $E$ in $M$ or in $H$ is asserted.
--
--   This is the admissibility step for the cyclic hull in the archimedean analysis of the cubic induction: the vectors of a fixed type $\tau$ (trivial rotation type for $\ell = 0$, the three-dimensional type cut out by the rotation Casimir for $\ell = 1$) inside the smallest translation- and derivative-stable subspace generated by a single type-$\tau$ vector of a smoothing module are confined to a finite-dimensional space, in the spirit of Harish-Chandra's admissibility theorem. It is used by [`LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
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
    (a : ℕ) (ha : a = 0 ∨ a = 1) (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf : f ∈ M)
    (hfτ : ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j f - WhittakerBlock.archDeriv j i f = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 f - WhittakerBlock.archDeriv 1 0 f) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 f - WhittakerBlock.archDeriv 1 0 f)) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 f - WhittakerBlock.archDeriv 2 0 f) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 f - WhittakerBlock.archDeriv 2 0 f)) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 f - WhittakerBlock.archDeriv 2 1 f) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 f - WhittakerBlock.archDeriv 2 1 f)) + (2 : ℂ) • f = 0)))
    (H : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hHM : H ≤ M) (hfH : f ∈ H)
    (hHK : (∀ w ∈ H, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ H))
    (hHD : (∀ w ∈ H, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H))
    (hHmin : ∀ H' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), H' ≤ M → f ∈ H' →
      (∀ w ∈ H', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ H') →
      (∀ w ∈ H', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H') → H ≤ H') :
    ∃ E : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), FiniteDimensional ℂ ↥E ∧
      ∀ u ∈ H, ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j u - WhittakerBlock.archDeriv j i u = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 u - WhittakerBlock.archDeriv 1 0 u) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 u - WhittakerBlock.archDeriv 1 0 u)) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 u - WhittakerBlock.archDeriv 2 0 u) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 u - WhittakerBlock.archDeriv 2 0 u)) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 u - WhittakerBlock.archDeriv 2 1 u) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 u - WhittakerBlock.archDeriv 2 1 u)) + (2 : ℂ) • u = 0)) → u ∈ E := by sorry
