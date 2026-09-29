-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_stable_submodule_separating_signProjection_of_doubleSlotCoeffMap
-- name    : LanglandsTunnell.CubicInduction.exists_stable_submodule_separating_signProjection_of_doubleSlotCoeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/dea22a64-ce3a-584c-a843-ccba07dd56b8
-- title:
--   Separating O(3)-stable submodule for the sign-projected double coefficient
-- statement:
--   Throughout, $G=\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ is `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group of degree $3$ over the adele ring of $\mathbb{Q}$, and the ambient space is the space of complex-valued functions on $G$. Fixed data: a $\mathbb{C}$-submodule $M$ of that function space, and a character $\omega$ of the idele class group $(\mathbb{A}_{\mathbb{Q}})^{\times}$ with values in $\mathbb{C}^{\times}$.
--
--   The first group of hypotheses restricts the members of $M$. `h1`: every $w\in M$ is archimedean-smooth in the sense of [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) (for each $g$, the map $e\mapsto w(g\cdot\mathrm{archRealLift3}\,e)$ is $C^{\infty}$ on the set of real $3\times 3$ matrices of non-zero determinant, where `archRealLift3` sends $e$ to the corresponding unit of $G$ when it is one and to $1$ otherwise); the Whittaker transform `whittaker3` of $w$, formed with the carrier data `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)` (empty defining set, trivial level subgroups and generators, and the adelic additive Haar measure conditioned to the adelic box) and the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), i.e. the triple integral of $w(u(x,y,z)g)\psi(-(x+y))$ over the upper unipotent, is archimedean-smooth as well; every iterated right derivative of $w$ along a finite list of slots $(i,j)$, built from `WhittakerBlock.archDeriv i j` (the derivative at $s=0$ of $g\mapsto w(g\cdot\mathrm{archRealLift3}(1+s\,E_{ij}))$), is continuous; and $w$ is left invariant under the rational points $\mathrm{GL}_3(\mathbb{Q})$ embedded by `globalPointsGL`. `h3`: for each $w\in M$ there is a finite set $s$ of functions such that, for every $k\in G$ with trivial component at every height-one prime (`componentAt3`) and archimedean component (`archComponent3`) in `orth3` $=\{k\mid k^{\mathsf T}k=1\}$, the right translate $g\mapsto w(gk)$ lies in the $\mathbb{C}$-span of $s$ — finiteness of $M$ under this orthogonal right action. `h4`: $M$ is stable under those right translations. `h5`: $M$ is stable under all nine operators `WhittakerBlock.archDeriv i j`. `h10`: there exists a form $B$ on two function arguments which, on $M$, is hermitian, linear in the first variable in the stated sense, positive ($0<\mathrm{Re}\,B(w,w)$ for $0\neq w\in M$), makes each `archDeriv i j` skew, and is invariant under the right translations of `h4`. `h11`: there are monic complex polynomial relations of degrees $N_1,N_2,N_3$ (coefficient families $a_1,a_2,a_3$ with top coefficient $1$) annihilating every $w\in M$ for the three Casimir-type operators `WhittakerBlock.casimir1` $=\sum_i\partial_{ii}$, `casimir2` $=\sum_{i,j}\partial_{ij}\partial_{ji}$ and `casimir3` $=\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$, the powers being taken as iterates. `h12`: every $v\in M$ has central character $\omega$ with respect to the scalar embedding `centralScalarGL`. `h13`: every $v\in M$ has polynomial growth: there is $N$ such that each iterated derivative of $v$ along a list of slots is bounded by $C\cdot \mathrm{gauge3}(g)^N$, where `gauge3` $g=\max(1,\ \text{archimedean gauge}\cdot\text{finite gauge})$.
--
--   Next, explicit data for two of the Casimir relations: natural numbers $N_2,N_3$, coefficient families $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ and $a_3:\mathrm{Fin}(N_3+1)\to\mathbb{C}$ with $a_2(N_2)=1$ (`ha₂`) and $a_3(N_3)=1$ (`ha₃`), and `hrel`, stating that $\sum_l a_2(l)\,\mathrm{casimir2}^{[l]}w=0$ and $\sum_l a_3(l)\,\mathrm{casimir3}^{[l]}w=0$ for all $w\in M$.
--
--   Expansion data: a real $\rho$, natural numbers $n,J$, an injective family of exponents $e:\mathrm{Fin}\,n\to\mathbb{C}$ (`he`) with $\mathrm{Re}\,e_i\le\rho$ for all $i$ (`hre`), and $\delta>0$ (`hδ`). The hypothesis `hexp` (a single implication with seven antecedents and a two-fold conclusion, summarised here) asserts: for every $N$ and every function $u$ on $G$ which has continuous iterated derivatives along all slot lists, is left $\mathrm{GL}_3(\mathbb{Q})$-invariant, has central character $\omega$, is archimedean-smooth, has finite-dimensional span of its orthogonal right translates as in `h3`, satisfies the two monic relations with coefficients $a_2$ and $a_3$, and satisfies the growth bound of exponent $N$ along every slot list, the Whittaker transform of $u$ admits two asymptotic expansions along the real diagonal torus $\mathrm{archRealLift3}(\mathrm{diag}(y_1y_2,y_2,1))$, with exponents $e_i$ and logarithmic powers $(\log\,\cdot)^j$, $j<J$, and error $O(y^{\rho+\delta})$: one with principal variable $y_1$ and coefficients $c\,i\,j\,y_2\,k$ continuous on $\{y_2>0\}\times G$, uniformly for $k$ in compacta and $y_2$ in compact subintervals of $(0,\infty)$, the coefficients themselves admitting a secondary expansion in $y_2$ with continuous coefficients $c'\,i\,j\,i'\,j'$ and the same error, together with a propagation clause stating that if all $c$-coefficients with strictly smaller $\mathrm{Re}\,e$ vanish identically and all $c'\,i\,j\,i'\,j'$ vanish, then $c\,i\,j$ vanishes; and a second, mirror-symmetric expansion with the roles of $y_1$ and $y_2$ interchanged.
--
--   Slot and representation data: indices $i_9,i_9'\in\mathrm{Fin}\,n$, $j_0,j_0'\in\mathrm{Fin}\,J$, a tuple $\nu:\mathrm{Fin}\,3\to\mathbb{C}$, and a $\mathbb{C}$-linear map $\Lambda$ from $M$ to functions on $G$, subject to three hypotheses. `hΛa`: for every $v\in M$ and all two coefficient families $(c_v,c_v')$ satisfying the four clauses of the first expansion above for $v$ (continuity of $c_v$ on $\{y_1>0\}\times G$ — the first slot being the $y_2$ variable — the uniform $y_1$-expansion of the Whittaker transform of $v$, continuity of $c_v'$, and the uniform secondary $y_2$-expansion of $c_v$), one has $\Lambda v = c_v'\,i_9\,j_0\,i_9'\,j_0'$; thus $\Lambda$ reads off the double expansion coefficient at the four fixed slots. `hΛb`: $\Lambda$ commutes with right translation by any $k'$ with trivial finite components and orthogonal archimedean component, i.e. $\Lambda(v(\cdot\,k'))(g)=(\Lambda v)(gk')$. `hΛc`: for all $v\in M$, all $c,d\in\mathrm{Fin}\,3$ and all $g$, the function $s\mapsto (\Lambda v)(g\cdot\mathrm{archRealLift3}(1+s\,E_{cd}))$ has derivative $(\Lambda(\mathrm{archDeriv}\,c\,d\,v))(g)$ at $s=0$.
--
--   Finally, the datum of a distinguished member. A sign character is encoded by $\varepsilon:\mathrm{Fin}\,3\to\mathrm{Fin}\,2$; $k_1\in G$ has archimedean component $1$ (`hk₁`); $\ell$ is a natural number with $\ell=0$ or $\ell=1$ (`hℓ`); $p\in\mathbb{C}[X_0,X_1,X_2]$ is homogeneous of degree $\ell$ (`hp`); and $v\in M$ (`hv`) satisfies two conditions. `hveq`: for every real upper-triangular $t$ (all entries below the diagonal zero) with positive diagonal entries and every $g$, $(\Lambda v)(\mathrm{archRealLift3}(t)\,g)=\bigl(\prod_a t_{aa}^{\,\nu_a+(1,0,-1)_a}\bigr)(\Lambda v)(g)$. `hvread`: for every real $3\times 3$ matrix $o$ with $o^{\mathsf T}o=1$ (written as $\sum_a o_{a,i}\,o_{a,j}=\delta_{ij}$), the $\varepsilon$-sign projection
--   $$\tfrac18\sum_{\tau:\mathrm{Fin}\,3\to\mathrm{Fin}\,2}(-1)^{\sum_a \varepsilon_a\tau_a}\,(\Lambda v)\bigl(\mathrm{archRealLift3}(\mathrm{diag}((-1)^{\tau_a}))\cdot(\mathrm{archRealLift3}(o)\,k_1)\bigr)$$
--   equals $\det(o)^{(\ell+\sum_a\varepsilon_a)\bmod 2}$ times the value of $p$ at the first column of $o$, that is the evaluation at $(o_{ij})$ of the image of $p$ under $X_a\mapsto X_{(a,0)}$.
--
--   Conclusion. There exist a $\mathbb{C}$-submodule $M'$ of the function space and a proof $hle$ that $M'\le M$ such that:
--
--   (1) $M'$ is stable under right translation by every $k\in G$ whose component at each height-one prime is $1$ and whose archimedean component lies in `orth3`;
--
--   (2) $M'$ is stable under all nine operators `WhittakerBlock.archDeriv i j`;
--
--   (3) every $u\in M'$ satisfies the same torus equivariance as $v$: for real upper-triangular $t$ with positive diagonal and all $g$, $(\Lambda u)(\mathrm{archRealLift3}(t)\,g)=\bigl(\prod_a t_{aa}^{\,\nu_a+(1,0,-1)_a}\bigr)(\Lambda u)(g)$;
--
--   (4) the $\varepsilon$-sign projection separates $M'$ on the orthogonal coset: if $u\in M'$ is such that the above projection of $\Lambda u$ at $\mathrm{archRealLift3}(o)\,k_1$ vanishes for every real $o$ with $o^{\mathsf T}o=1$, then $u=0$;
--
--   (5) there is $v'\in M'$ whose projected read reproduces that of $v$: for every real $o$ with $o^{\mathsf T}o=1$, the $\varepsilon$-sign projection of $\Lambda v'$ at $\mathrm{archRealLift3}(o)\,k_1$ equals $\det(o)^{(\ell+\sum_a\varepsilon_a)\bmod 2}$ times the value of $p$ at the first column of $o$.
--
--   This is an interface step in the archimedean analysis for the cubic induction in the Langlands–Tunnell argument: it replaces a module of automorphic functions on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with finiteness, growth, Casimir and positivity properties by a submodule, still stable under the orthogonal right action and the nine right derivatives, on which the $\varepsilon$-isotypic projection of the double Whittaker expansion coefficient is injective while the distinguished read of a given member is kept. It is derived from [`LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule), and is used in the vanishing statements for sign-isotypic reads of homogeneous degree $0$ and $1$ and for odd sign types.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_stable_submodule_separating_signProjection_of_doubleSlotCoeffMap.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_stable_submodule_separating_signProjection_of_doubleSlotCoeffMap
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
    (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
    (hveq : (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨v, hv⟩ g))
    (hvread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v, hv⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) :
    ∃ M' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∃ hle : M' ≤ M,
      (∀ w ∈ M', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M') ∧
      (∀ w ∈ M', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M') ∧
      (∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'), (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hle hu⟩ g)) ∧
      (∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'),
        (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) → u = 0) ∧
      ∃ (v' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv' : v' ∈ M'), ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v', hle hv'⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) := by sorry
