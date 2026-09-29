-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
-- name    : LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d302e530-9813-5abb-90ce-8128c5b24f8c
-- title:
--   Induced-picture package from a top-slot double leading Whittaker coefficient
-- statement:
--   Throughout, functions on $GL_3$ of the adeles of $\mathbb{Q}$ means functions `AdelicGL 3 (𝓞 ℚ) ℚ → ℂ`, where `AdelicGL 3 (𝓞 ℚ) ℚ` is $GL_3$ of the adele ring; `archRealLift3 e` denotes the adelic point attached to a real $3\times 3$ matrix $e$ (its unit if $e$ is invertible, and $1$ otherwise); `archDeriv i j` is the right derivative at $0$ along $1 + sE_{ij}$ in the archimedean direction, `casimir1`, `casimir2`, `casimir3` are the associated traces $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$; `IsArchSmooth3 φ` says that for every $g$ the map $e \mapsto φ(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{e : \det e \neq 0\}$; `orth3` is the set of points $k$ of $GL_3$ of the infinite adeles with $k^{\mathsf T}k = 1$; `whittaker3` of a function is its triple unipotent integral against the standard additive character `psiQ`, the measure being the conditioned adelic additive Haar measure attached to `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`; and `gauge3 ℚ g` is $\max(1, \mathrm{archGauge3}\,g \cdot \mathrm{finGauge3}\,g)$.
--
--   The data are a $\mathbb{C}$-submodule $M$ of functions on $GL_3$ of the adeles and a homomorphism $ω$ from the idele group to $\mathbb{C}^\times$, subject to the following hypotheses on $M$. `h1`: every $w \in M$ is arch-smooth, its Whittaker transform `whittaker3 … psiQ w` is arch-smooth, every iterated archimedean derivative $\mathrm{archDeriv}$-word applied to $w$ is continuous, and $w$ is left invariant under the rational points $GL_3(\mathbb{Q})$ embedded by `globalPointsGL`. `h3`: every $w \in M$ is $O(3)$-finite, in the sense that there is a finite set $s$ of functions such that for every $k$ whose component at each height-one prime of $𝓞_{\mathbb{Q}}$ is trivial and whose archimedean component lies in `orth3`, the right translate $g \mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$. `h4`: $M$ is stable under such right translations. `h5`: $M$ is stable under the nine operators $\mathrm{archDeriv}\,i\,j$. `h12`: every $v \in M$ has central character $ω$, i.e. $v(\mathrm{centralScalarGL}(z)g) = ω(z)v(g)$. `h13`: every $v \in M$ has moderate growth uniformly in derivative words: there is $N$ such that each $\mathrm{archDeriv}$-word of $v$ is bounded by $C\cdot \mathrm{gauge3}\,g^{N}$ for some constant depending on the word.
--
--   Further data: natural numbers $N_2, N_3$ and coefficient families $a_2 : \mathrm{Fin}(N_2+1) \to \mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ that are monic (`ha₂`, `ha₃`: the last coefficients are $1$), together with `hrel`: every $w \in M$ satisfies $\sum_l a_2(l)\,\mathrm{casimir2}^{[l]}w = 0$ and $\sum_l a_3(l)\,\mathrm{casimir3}^{[l]}w = 0$. Also a real $ρ$, naturals $n, J$, an injective family of exponents $e : \mathrm{Fin}\,n \to \mathbb{C}$ (`he`) with $\mathrm{Re}\,e_i \le ρ$ for all $i$ (`hre`), and a real $δ > 0$.
--
--   The hypothesis `hexp` supplies joint expansions for all admissible functions: for every $N : \mathbb{N}$ and every $u$ such that all $\mathrm{archDeriv}$-words of $u$ are continuous, $u$ is $GL_3(\mathbb{Q})$-left invariant, $u$ has central character $ω$, $u$ is arch-smooth, $u$ is $O(3)$-finite in the span sense of `h3`, $u$ satisfies the two monic relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u = 0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u = 0$, and every $\mathrm{archDeriv}$-word of $u$ is bounded by $C\cdot\mathrm{gauge3}^N$, two expansions of the Whittaker function of $u$ along the diagonal flow $\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2, y_2, 1)$ exist, one in $y_1$ and one in $y_2$ (the two conjuncts being mirror images with the roles of $y_1$ and $y_2$ exchanged). Each consists of: coefficients $c : \mathrm{Fin}\,n \to \mathrm{Fin}\,J \to \mathbb{R} \to GL_3(\mathbb{A}) \to \mathbb{C}$ jointly continuous on $\{(y,k) : y > 0\}$; a main bound stating that for every compact $K$ and every $b \ge 1$ there is $C$ with $\bigl\|W_u(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k) - \sum_{i,j} c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j}\bigr\| \le C y_1^{ρ+δ}$ for $k \in K$, $b^{-1}\le y_2 \le b$ and $0 < y_1 \le 1$; secondary coefficients $c'$, each continuous, with $\|c_{ij}(y_2,k) - \sum_{i',j'} c'_{ij i' j'}(k)\,y_2^{e_{i'}}(\log y_2)^{j'}\| \le C y_2^{ρ+δ}$ uniformly for $k$ in compacta and $0 < y_2 \le 1$; and a vanishing clause: for each $(i,j)$, if $c_{i''j''}$ vanishes identically for all exponents with $\mathrm{Re}\,e_{i''} < \mathrm{Re}\,e_i$ and all $c'_{iji'j'}$ vanish, then $c_{ij}$ vanishes for all $y > 0$.
--
--   Finally, a distinguished $w \in M$ (`hw`) is fixed, with complex scalars $λ_1, λ_2, λ_3$ such that $\mathrm{casimir1}\,w = λ_1 w$, $\mathrm{casimir2}\,w = λ_2 w$, $\mathrm{casimir3}\,w = λ_3 w$ (`hC1`–`hC3`); a first-layer coefficient family $c$ for $w$ with joint continuity `hcc` and the $y_1$-expansion bound `hce` of the shape just described; a second-layer family $c'$ with continuity `hc'c` and the $y_2$-expansion bound `hc'e`; indices $i_9, i_9' \in \mathrm{Fin}\,n$ and $j_0, j_0' \in \mathrm{Fin}\,J$; and four extremality hypotheses: `hbot₁`, that $c_{ij}(y_2,k) = 0$ for all $y_2 > 0$ and all $k$ whenever $\mathrm{Re}\,e_i < \mathrm{Re}\,e_{i_9}$; `hbot₂`, that $c'_{i_9 j_0 i' j'} = 0$ whenever $\mathrm{Re}\,e_{i'} < \mathrm{Re}\,e_{i_9'}$; `htop₁`, that $c_{i_9 j}(y_2,k) = 0$ for all $y_2 > 0$ and all $k$ when $j_0 < j$; `htop₂`, that $c'_{i_9 j_0 i_9' j'} = 0$ when $j_0' < j'$. A point $k_0$ is given with $c'_{i_9 j_0 i_9' j_0'}(k_0) \neq 0$ (`hk₀`).
--
--   Conclusion: there exist a $\mathbb{C}$-submodule $V$ of functions on $GL_3$ of the adeles and a point $k_1$ such that, writing $F = c'_{i_9 j_0 i_9' j_0'}$:
--
--   (i) $F \in V$; (ii) the archimedean component of $k_1$ is trivial; (iii) there is a real $3\times 3$ matrix $o$ with $\sum_a o_{ai}o_{aj} = δ_{ij}$ for all $i,j$ such that $F(\mathrm{archRealLift3}\,o \cdot k_1) \neq 0$; (iv) every $G \in V$ is continuous; (v) every $G \in V$ is arch-smooth and satisfies $\mathrm{casimir1}\,G = λ_1 G$, $\mathrm{casimir2}\,G = λ_2 G$, $\mathrm{casimir3}\,G = λ_3 G$; (vi) every $G \in V$ is equivariant for real upper-triangular matrices with positive diagonal: for every $t$ with $t_{ij} = 0$ when $j < i$ and $t_{ii} > 0$, and every $g$,
--   $$G(\mathrm{archRealLift3}\,t \cdot g) = \Bigl(\prod_{a} t_{aa}^{\,ν_a + ρ_a}\Bigr) G(g), \qquad ν = (e_{i_9}-1,\; e_{i_9'}-e_{i_9},\; λ_1 - e_{i_9'}+1),\quad ρ = (1,0,-1);$$
--   (vii) $V$ is stable under right translation by every $k'$ with trivial components at all height-one primes and archimedean component in `orth3`; (viii) every $G \in V$ is $O(3)$-finite in the span sense of `h3`; (ix) $V$ is closed under the nine archimedean flows: for every $G \in V$ and every pair $c_0, d_0 \in \mathrm{Fin}\,3$ there is $G' \in V$ such that for every $g$ the function $s \mapsto G(g\cdot \mathrm{archRealLift3}(\mathrm{id} + sE_{c_0 d_0}))$ has derivative $G'(g)$ at $s = 0$ (in the sense of `HasDerivAt`); and (x) every $G \in V$ is realised as a double coefficient of a member of $M$: there are $v \in M$ and families $cv$, $cv'$ with $cv$ jointly continuous on $\{y>0\}$, satisfying the $y_1$-expansion bound for the Whittaker function of $v$ with error $C y_1^{ρ+δ}$, with $cv'$ continuous and satisfying the secondary $y_2$-expansion bound with error $C y_2^{ρ+δ}$, and $G = cv'_{i_9 j_0 i_9' j_0'}$.
--
--   This is the assembly step of the second-slot analysis in the Langlands–Tunnell cubic induction on $GL_3$: from a double leading coefficient of the Whittaker expansion of a Casimir eigenvector in a smoothing module, non-vanishing at one point and read at the top logarithmic powers in both slots, it produces a space of functions that is right $O(3)$-stable and $O(3)$-finite, closed under the nine archimedean flows, carries the three Casimir scalars of the eigenvector, and transforms by the explicit character $ν + (1,0,-1)$ of the positive upper-triangular real matrices — that is, a $(\mathfrak{g}, O(3))$-stable space of smooth $K$-finite vectors in the induced picture of the principal series with parameter $ν$ determined by the exponents $e_{i_9}, e_{i_9'}$ and $λ_1$ — together with the fact that every member of it is such a double coefficient of a member of the module. It is cited by `leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
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
    (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw : w ∈ M) (lam₁ lam₂ lam₃ : ℂ)
    (hC1 : WhittakerBlock.casimir1 w = lam₁ • w) (hC2 : WhittakerBlock.casimir2 w = lam₂ • w)
    (hC3 : WhittakerBlock.casimir3 w = lam₃ • w)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcc : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (hce : (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)))
    (c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc'c : ∀ i j i' j', Continuous (c' i j i' j'))
    (hc'e : (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖c i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, c' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (i9 i9' : Fin n) (j₀ j₀' : Fin J)
    (hbot₁ : ∀ (i : Fin n) (j : Fin J), (e i).re < (e i9).re → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, c i j y₂ k = 0)
    (hbot₂ : ∀ (i' : Fin n) (j' : Fin J), (e i').re < (e i9').re → ∀ k, c' i9 j₀ i' j' k = 0)
    (htop₁ : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, c i9 j y₂ k = 0)
    (htop₂ : ∀ j' : Fin J, (j₀' : ℕ) < (j' : ℕ) → ∀ k, c' i9 j₀ i9' j' k = 0)
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₀ : c' i9 j₀ i9' j₀' k₀ ≠ 0) :
    ∃ (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ),
      (c' i9 j₀ i9' j₀' ∈ V ∧
      archComponent3 (𝓞 ℚ) ℚ k₁ = 1 ∧
      (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧
        c' i9 j₀ i9' j₀' (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) ∧
      (∀ G ∈ V, Continuous G) ∧
      (∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ V, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ ((![e i9 - 1, e i9' - e i9, lam₁ - e i9' + 1] : Fin 3 → ℂ) a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
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
        G = cv' i9 j₀ i9' j₀')) := by sorry
