-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/b22bfc74-5a26-5005-8021-c858b0ff1082
-- title:
--   Specialising a flat family of local Rankin–Selberg functional equations
-- statement:
--   Throughout, $K$ is a number field, $v$ a non-zero prime of $\mathcal{O}_K$, $F = K_v$ the associated completion with valuation ring $\mathcal{O}_v$, and $q_v = \operatorname{absNorm}(v)$ the absolute norm of $v$. An element $\varpi$ of $\mathcal{O}_v$ is fixed whose image $\pi$ in $F$ is non-zero (`hπ`) and satisfies $\mathrm{v}(\pi) = \exp(-1)$ (`hϖ`), i.e. $\varpi$ is a uniformiser; a natural number $b$ is fixed. Both $F$ and $\mathrm{GL}_2(F)$ carry their Borel measurable structures. Write $K_0 =$ [`AdelicDock.localLevelOne (𝓞 K) K v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) for the subgroup of $\mathrm{GL}_2(F)$ consisting of those $g$ whose image under the place-$v$ embedding into $\mathrm{GL}_2$ of the finite adele ring lies in the level-one subgroup at level the unit ideal; write $N$ for the range of `unipotentGL2Hom`, the group of upper unipotent matrices $\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)$, $\mathrm{unipotent}(x)$ for such a matrix, $\mathrm{scalarPi}(\pi) = \mathrm{diag}(\pi,\pi)$ and $\mathrm{diagUnitGL2}(x) = \mathrm{diag}(x,1)$ for $x \in F^\times$. Finally $|a| =$ `modulus` $a$ denotes the module of $a \in F$, i.e. the value of the distributive Haar character at $a$ when $a \neq 0$ and $0$ otherwise.
--
--   **Level subgroups** (`hKb₁`, `hKb₁K`, `hKb₁c`, `hKb₂`, `hKb₂K`, `hKb₂c`): two subgroups $K_{b,1}, K_{b,2}$ of $\mathrm{GL}_2(F)$ are given, each open, each contained in $K_0$, and each containing every $k \in K_0$ all of whose entries of $k - 1$ have valuation $\le \exp(-b)$.
--
--   **The two functions $A_1, A_2 : \mathrm{GL}_2(F) \to \mathbb{C}$** (`hA₁`, `hA₂`): each is invariant under right translation by some open subgroup of $\mathrm{GL}_2(F)$.
--
--   **The two families $E_1, E_2 : \mathbb{Z} \to \mathrm{GL}_2(F) \to \mathbb{C}$** (`hE₁K`, `hE₂K`, `hAE₁`, `hAE₂`, `hE₁fin`, `hE₂fin`): for each $i \in \mathbb{Z}$, $E_j(i)$ is invariant under right translation by $K_{b,j}$; the product $A_j \cdot E_j(i)$ is left $N$-invariant, i.e. $A_j(\mathrm{unipotent}(x)g)\,E_j(i)(\mathrm{unipotent}(x)g) = A_j(g)E_j(i)(g)$ for all $x \in F$ and $g$; and each family is locally finite in the index: for every compact $C \subseteq \mathrm{GL}_2(F)$ the set of $i$ for which $E_j(i)$ is non-zero somewhere on $C$ is finite.
--
--   **The sections and their specialisations** (`hw₁`, `hw₂`, `hwc₁`, `hwc₂`): functions $w_1, w_2 : \mathbb{C} \to \mathrm{GL}_2(F) \to \mathbb{C}$ and $wc_1, wc_2 : \mathrm{GL}_2(F) \to \mathbb{C}$ and a real number $u_1$ are given with $w_j(u)(g) = \sum^{\mathrm{f}}_{i \in \mathbb{Z}} q_v^{-iu}\,E_j(i)(g)$ for all $g$ whenever $\operatorname{Re} u > u_1$, and $wc_j(g) = \sum^{\mathrm{f}}_{i \in \mathbb{Z}} E_j(i)(g)$, the sums being finitely supported sums over $\mathbb{Z}$. A function $\gamma : \mathbb{C} \to \mathbb{C}$ and an integer $e$ are also fixed.
--
--   The assertion is then the following, for all Haar measures $\mu_2$ on $\mathrm{GL}_2(F)$, $\mu_{N}$ on $N$ and $\nu$ on $F^\times$. Write $\tilde\mu_2$ for $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ relative to $\mu_N$, and
--   $$\Psi(s; W, F_0) = \int_{\mathrm{GL}_2(F)} W(g)F_0(g)\,|\det g|^{\,s - 1/2}\,d\tilde\mu_2(g)$$
--   for the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) taken with $\delta(g) = |\det g|$. Four hypotheses are assumed.
--
--   *(i)–(ii) Torus-shell vanishing for $A_1$ and for $A_2$.* For every $k_0 \in K_0$, every monoid homomorphism $\eta : F^\times \to \mathbb{C}^\times$ and every $c \in \mathbb{N}$ with `HasConductorExponentAt K v η c` (that is, $\eta$ is trivial on the higher unit set of level $c$, and for every $m < c$ it is non-trivial on the higher unit set of level $m$) and $c \le b$, there is a finite set $T \subseteq \mathbb{Z} \times \mathbb{Z}$ such that for all $n = (n_1,n_2) \notin T$,
--   $$\int_{\{|u| = 1\}} \Bigl(\int_{K_{b,j}} A_j\bigl(\mathrm{diag}(\pi,\pi)^{n_2}\,\mathrm{diag}(\varpi^{\,n_1}u,1)\,k_0k\bigr)\,d\mu_2(k)\Bigr)\eta(u)\,d\nu(u) = 0,$$
--   the outer integral being over the units $u$ of $F$ with $\mathrm{v}(u) = 1$; hypothesis (i) is this for $j = 1$ with $K_{b,1}$, hypothesis (ii) the same for $j = 2$ with $K_{b,2}$.
--
--   *(iii) The functional equation along the family.* There is $u_0 \in \mathbb{R}$ such that for every $u$ with $\operatorname{Re} u > u_0$ there are polynomials $P, P^\vee \in \mathbb{C}[X]$, integers $m, m^\vee$ and reals $\sigma_2, \sigma_3$ for which: $g \mapsto A_1(g)w_1(u)(g)|\det g|^{s-1/2}$ is $\tilde\mu_2$-integrable for $\operatorname{Re} s > \sigma_2$; $g \mapsto A_2(g)w_2(u)(g)|\det g|^{s-1/2}$ is $\tilde\mu_2$-integrable for $\operatorname{Re} s > \sigma_3$; $\Psi(s; A_1, w_1(u)) = q_v^{\,ms}P(q_v^{-s})$ for $\operatorname{Re} s > \sigma_2$; $\Psi(s; A_2, w_2(u)) = q_v^{\,m^\vee s}P^\vee(q_v^{-s})$ for $\operatorname{Re} s > \sigma_3$; and, for all $s \in \mathbb{C}$,
--   $$q_v^{\,m^\vee s}P^\vee(q_v^{-s}) = \bigl(\gamma(s)\,q_v^{\,eu}\bigr)\cdot\bigl(q_v^{-ms}P(q_v^{\,s})\bigr).$$
--
--   *(iv) Integrability of the specialisations.* There is $\sigma_c \in \mathbb{R}$ such that for every $s$ with $\operatorname{Re} s > \sigma_c$ both $g \mapsto A_1(g)wc_1(g)|\det g|^{s-1/2}$ and $g \mapsto A_2(g)wc_2(g)|\det g|^{s-1/2}$ are $\tilde\mu_2$-integrable.
--
--   **Conclusion.** There exist polynomials $P, P^\vee \in \mathbb{C}[X]$, integers $m, m^\vee$ and reals $\sigma_2, \sigma_3$ such that:
--
--   1. for every $s$ with $\operatorname{Re} s > \sigma_2$, the function $g \mapsto A_1(g)wc_1(g)|\det g|^{s-1/2}$ is $\tilde\mu_2$-integrable;
--
--   2. for every $s$ with $\operatorname{Re} s > \sigma_3$, the function $g \mapsto A_2(g)wc_2(g)|\det g|^{s-1/2}$ is $\tilde\mu_2$-integrable;
--
--   3. $\Psi(s; A_1, wc_1) = q_v^{\,ms}\,P(q_v^{-s})$ for every $s$ with $\operatorname{Re} s > \sigma_2$;
--
--   4. $\Psi(s; A_2, wc_2) = q_v^{\,m^\vee s}\,P^\vee(q_v^{-s})$ for every $s$ with $\operatorname{Re} s > \sigma_3$;
--
--   5. for every $s \in \mathbb{C}$,
--   $$q_v^{\,m^\vee s}P^\vee(q_v^{-s}) = \gamma(s)\cdot\bigl(q_v^{-ms}P(q_v^{\,s})\bigr),$$
--   that is, the functional equation of (iii) with the same $\gamma$ but with the factor $q_v^{\,eu}$ removed.
--
--   This is the closing step in the proof of the local $\mathrm{GL}_3 \times \mathrm{GL}_2$ Rankin–Selberg functional equation in the second variable: the functional equation is first established for the second factors $w_j(u)$ of a family deformed by $|\cdot|^{u}$ with $\operatorname{Re} u$ large, where the integrals converge absolutely, and is here transported to the specialisation $wc_j = \sum_i E_j(i)$ at $u = 0$, the $\gamma$-factor being unchanged. The proof uses the rationality and torus-expansion result [`LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero`](thm.html#LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero), and the statement is in turn used in [`LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2`](thm.html#LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)

    (Kb₁ Kb₂ : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hKb₁ : IsOpen (Kb₁ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKb₁K : Kb₁ ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKb₁c : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb₁)
    (hKb₂ : IsOpen (Kb₂ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKb₂K : Kb₂ ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKb₂c : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb₂)

    (A₁ A₂ : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hA₁ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A₁ (g * k) = A₁ g)
    (hA₂ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A₂ (g * k) = A₂ g)

    (E₁ E₂ : ℤ → GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hE₁K : ∀ i : ℤ, ∀ k ∈ Kb₁, ∀ g : GL (Fin 2) (v.adicCompletion K), E₁ i (g * k) = E₁ i g)
    (hE₂K : ∀ i : ℤ, ∀ k ∈ Kb₂, ∀ g : GL (Fin 2) (v.adicCompletion K), E₂ i (g * k) = E₂ i g)
    (hAE₁ : ∀ (i : ℤ) (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A₁ (unipotent x * g) * E₁ i (unipotent x * g) = A₁ g * E₁ i g)
    (hAE₂ : ∀ (i : ℤ) (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A₂ (unipotent x * g) * E₂ i (unipotent x * g) = A₂ g * E₂ i g)
    (hE₁fin : ∀ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, E₁ i g ≠ 0}.Finite)
    (hE₂fin : ∀ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, E₂ i g ≠ 0}.Finite)

    (w₁ w₂ : ℂ → GL (Fin 2) (v.adicCompletion K) → ℂ) (wc₁ wc₂ : GL (Fin 2) (v.adicCompletion K) → ℂ) (u₁ : ℝ)
    (hw₁ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₁ u g = ∑ᶠ i : ℤ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₁ i g)
    (hw₂ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₂ u g = ∑ᶠ i : ℤ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₂ i g)
    (hwc₁ : ∀ g : GL (Fin 2) (v.adicCompletion K), wc₁ g = ∑ᶠ i : ℤ, E₁ i g)
    (hwc₂ : ∀ g : GL (Fin 2) (v.adicCompletion K), wc₂ g = ∑ᶠ i : ℤ, E₂ i g)

    (γ : ℂ → ℂ) (e : ℤ) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],

      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb₁ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A₁ (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb₂ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A₂ (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →

      (∃ u₀ : ℝ, ∀ u : ℂ, u₀ < u.re →
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₁ g * w₁ u g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₂ g * w₂ u g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A₁ (w₁ u) =
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A₂ (w₂ u) =
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
              (γ s * (Ideal.absNorm v.asIdeal : ℂ) ^ ((e : ℂ) * u)) *
                ((Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →

      (∃ σc : ℝ, ∀ s : ℂ, σc < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₁ g * wc₁ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) ∧
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₂ g * wc₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) →

      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (A₁ g * wc₁ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (A₂ g * wc₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion K) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
              s A₁ wc₁ =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion K) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
              s A₂ wc₂ =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            γ s * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ s))) := by sorry
