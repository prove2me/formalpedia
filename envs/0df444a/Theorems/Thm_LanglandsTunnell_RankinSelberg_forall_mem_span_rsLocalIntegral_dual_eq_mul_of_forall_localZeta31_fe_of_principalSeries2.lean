-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d3ec7003-b5c1-54e6-989a-23b8bdabb22e
-- title:
--   Multiplicativity of the GL₃timesGL₂ local γ-factor in principal series
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$, write $q = \mathrm{N}(p)$ for the absolute norm of `p.asIdeal`, and write $|\cdot|$ for the normalised modulus `modulus` on the completion $\mathbb{Q}_p =$ `p.adicCompletion ℚ` (which agrees with the norm). Throughout, $\iota =$ `iotaGL` is the embedding $\mathrm{GL}_2 \to \mathrm{GL}_3$, $g \mapsto \mathrm{diag}(g,1)$; for a function $W$ on $\mathrm{GL}_3$, `dualWhittakerFn3` $W$ is $g \mapsto W(w_3\,{}^t g^{-1})$ with $w_3 =$ `longWeyl3` the $3\times 3$ antidiagonal permutation matrix; `transposeInv3` and `transposeInvN` denote $g \mapsto {}^t g^{-1}$; `weylPrime3` is the permutation matrix interchanging the last two coordinates of $\mathbb{Q}_p^3$; the multiplicative measure on $\mathbb{Q}_p^\times$ used throughout is the pullback along $u \mapsto u$ of `mulMeasure (selfDualHaarAt ℚ p)`, i.e. the self-dual additive Haar measure divided by $|x|$ and restricted away from $0$.
--
--   **The $\mathrm{GL}_3$ datum.** A function $W_3^{\mathrm{base}} : \mathrm{GL}_3(\mathbb{Q}_p) \to \mathbb{C}$ is given, subject to: `hW₃law`, that $W_3^{\mathrm{base}}(u(x,y,z)g) = \psi_p^{-1}(x+y)\,W_3^{\mathrm{base}}(g)$ for all $x,y,z \in \mathbb{Q}_p$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y,z$ and $\psi_p$ is the local component `StandardAddChar.psiLocal ℚ p` of the standard adelic additive character; `hW₃sm`, that there is an open subgroup $U_v \le \mathrm{GL}_3(\mathbb{Q}_p)$ under which $W_3^{\mathrm{base}}$ is right invariant; `hW₃ne`, that $W_3^{\mathrm{base}} \ne 0$; `hω₃`, that $W_3^{\mathrm{base}}(t\cdot h) = \omega_3(t) W_3^{\mathrm{base}}(h)$ for a fixed character $\omega_3 : \mathbb{Q}_p^\times \to \mathbb{C}^\times$ and all scalar matrices $t$; and `hW₃irr`, that every nonzero $W$ in `gl3CyclicSubspace` $W_3^{\mathrm{base}}$ — the $\mathbb{C}$-span of the right translates $g \mapsto W_3^{\mathrm{base}}(gh)$ — has $W_3^{\mathrm{base}}$ in its own cyclic span.
--
--   **The gauge hypothesis `hWgauge`.** There are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, in terms of the three quantities $\mathrm{d}(h) = |\det h|$ (`detSize`), $\mathrm{r}(h)$ the maximum of the norms of the three entries of the last row (`lastRowSup`), and $\mathrm{m}(h)$ the maximum of the norms of the three $2\times 2$ minors formed from the last two rows (`minorSup`), the function $W_3^{\mathrm{base}}$ vanishes at every $h$ failing both inequalities $\mathrm{d}(h)\mathrm{r}(h)/\mathrm{m}(h)^2 \le B$ and $\mathrm{m}(h)/\mathrm{r}(h)^2 \le B$, while where both hold one has $\|W_3^{\mathrm{base}}(h)\| \le C\big/\big((\mathrm{d}(h)\mathrm{r}(h)/\mathrm{m}(h)^2)(\mathrm{m}(h)/\mathrm{r}(h)^2)\big)^t$.
--
--   **Characters and constants.** A pair of characters $\chi_0, \chi_1 : \mathbb{Q}_p^\times \to \mathbb{C}^\times$ is given, indexed by `Fin 2`, together with integers $c_{\chi}(i) \in \mathbb{N}$ such that (`hcχ`) $\chi_i$ is trivial on `higherUnitsAt ℚ p (cχ i)`, the set of units $u$ with $|u| = 1$ and either $c_\chi(i) = 0$ or $|u-1| \le q^{-c_\chi(i)}$; also constants $C_i \in \mathbb{C}$ and integers $k_i \in \mathbb{Z}$ for $i \in \{0,1\}$.
--
--   **The $(3,0)$–$(3,1)$ functional equations `h31`.** For each $i$ and each $g \in \mathrm{GL}_3(\mathbb{Q}_p)$ there exist $Q_1, Q_2 \in \mathbb{C}[X]$ with $Q_2 \ne 0$, an integer $n$ and reals $\sigma_0, \sigma_1$ such that: the integrand $a \mapsto W_3^{\mathrm{base}}(\iota(\mathrm{diag}(a,1))g)\chi_i(a)|a|^{s-1}$ is integrable for $\mathrm{Re}\, s > \sigma_0$ (`IsLocalZeta30ConvergentAbove`); for such $s$ the zeta integral `localZeta30` $= \int_{\mathbb{Q}_p^\times} W_3^{\mathrm{base}}(\iota(\mathrm{diag}(a,1))g)\chi_i(a)|a|^{s-1}$ satisfies $Z_{3,0}(s,g)\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ns}$; the integrand $(a,x) \mapsto (\mathrm{dualWhittakerFn3}\,W_3^{\mathrm{base}})(\iota(\mathrm{diag}(a,1))\,n_{21}(x)\,w_3'\,{}^tg^{-1})\,\chi_i^{-1}(a)|a|^{s-1}$, with $n_{21}(x)$ the lower unipotent matrix `lowerUnipotent21` and $w_3' =$ `weylPrime3`, is integrable on the product of the multiplicative and the self-dual additive measures for $\mathrm{Re}(1-s) > \sigma_1$ (`IsLocalZeta31ConvergentAbove`); and for $\mathrm{Re}(1-s) > \sigma_1$ the dual integral `localZetaDual31`, namely `localZeta31` of `dualWhittakerFn3` $W_3^{\mathrm{base}}$ against $\chi_i^{-1}$ at $1-s$ and the point $w_3'\,{}^tg^{-1}$, satisfies $Z^\vee_{3,1}(1-s,g)\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ns}\cdot\big(C_i\,q^{k_i s}\big)$. Thus the same rational datum $(Q_1,Q_2,n)$ computes both sides and the ratio is the monomial $\gamma_i(s) = C_i q^{k_i s}$.
--
--   **The $\mathrm{GL}_2$ datum.** An ideal $N$ of the ring of integers of $\mathbb{Q}$ with $N \ne \bot$ is given, and a function $w_2^{\mathrm{base}} : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ subject to: `hw₂law`, $w_2^{\mathrm{base}}(n(x)g) = \psi_p(x) w_2^{\mathrm{base}}(g)$ for $n(x)$ the upper unipotent matrix; `hw₂K`, right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback under the local embedding $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathrm{GL}_2(\widehat{\mathbb{Q}})$ of the finite-adelic level-$N$ subgroup; `hw₂ne`, $w_2^{\mathrm{base}} \ne 0$; and `hw₂irr`, that every nonzero element $w$ of the span $V$ of the right translates of $w_2^{\mathrm{base}}$ has $w_2^{\mathrm{base}}$ in the span of the right translates of $w$.
--
--   **The principal-series embedding `hPS`.** There is a $\mathbb{C}$-linear endomorphism $\Phi$ of the space of functions $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ which commutes with right translation on $V$, is injective on $V$, and carries $V$ into `principalSeries2 p χ`: the space of locally constant $f$ invariant under left multiplication by upper unipotent matrices and satisfying $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\sqrt{|a_0|/|a_1|}\,f(g)$.
--
--   **Level and uniformiser.** A natural number $b$ with $p^b \mid N$ and $p^{b+1} \nmid N$ (`hNb`), and an element $\varpi$ of the valuation ring whose image in $\mathbb{Q}_p$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), i.e. a uniformiser.
--
--   **Growth `hw₂gr`.** There are reals $C, A$ with $\|w_2^{\mathrm{base}}(\mathrm{diag}(\varpi^m,1)\,k)\| \le C\,q^{Am}$ for all integers $m \ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178).
--
--   **Torus-shell finiteness `hβ`.** For every $g_3 \in \mathrm{GL}_3(\mathbb{Q}_p)$, every $k_0 \in \mathrm{GL}_2(\mathbb{Q}_p)$, every character $\eta$ of $\mathbb{Q}_p^\times$ having conductor exponent $c$ in the sense of `HasConductorExponentAt` (trivial on `higherUnitsAt ℚ p c`, and nontrivial on `higherUnitsAt ℚ p m` for every $m < c$) with $c \le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$, there is a finite set $T \subset \mathbb{Z}\times\mathbb{Z}$ such that for every $n = (n_1,n_2) \notin T$ both of the following vanish: the integral over the unit shell $\{u : |u| = 1\}$, against $\eta(u)$ and the multiplicative measure, of $\int_{K_b} W_3^{\mathrm{base}}\big(\iota(\varpi^{n_2}I_2 \cdot \mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)\,g_3\big)\,d\mu_2(k)$, and the same expression with $W_3^{\mathrm{base}}(\cdot\,g_3)$ replaced by its `dualWhittakerFn3` and $k$ replaced by ${}^t k^{-1}$; here $K_b =$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178).
--
--   **The Weyl element `w₀p`.** An element $w_{0,p} \in \mathrm{GL}_2(\mathbb{Q}_p)$ whose matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **Conclusion.** For every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ (with the Borel structure `localGLBorel`) and every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, the subgroup of upper unipotent matrices, and for every $w_2$ in the span $V$ of the right translates of $w_2^{\mathrm{base}}$ and every $W_3$ in `gl3CyclicSubspace` $W_3^{\mathrm{base}}$, there exist $P, P^\vee \in \mathbb{C}[X]$, integers $m, m^\vee$ and reals $\sigma_2, \sigma_3$ such that, writing $\nu = \mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$ and $\delta(g) = |\det g|$:
--
--   (i) for every $s$ with $\mathrm{Re}\, s > \sigma_2$, the function $g \mapsto W_3(\iota g)\,w_2(g)\,\delta(g)^{s-1/2}$ is $\nu$-integrable;
--
--   (ii) for every $s$ with $\mathrm{Re}\, s > \sigma_3$, the function $g \mapsto (\mathrm{dualWhittakerFn3}\,W_3)(\iota g)\cdot\big(\delta(g)\,w_2(w_{0,p}\,{}^tg^{-1})\big)\cdot\delta(g)^{s-1/2}$ is $\nu$-integrable;
--
--   (iii) for every $s$ with $\mathrm{Re}\, s > \sigma_2$, the Rankin–Selberg local integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) with data $\mu_2$, the unipotent subgroup, $\mu_{N_2}$, the modulus $\delta$, the $\mathrm{GL}_3$ input $g \mapsto W_3(\iota g)$ and the $\mathrm{GL}_2$ input $w_2$ equals $q^{ms}\,P(q^{-s})$;
--
--   (iv) for every $s$ with $\mathrm{Re}\, s > \sigma_3$, the same local integral with inputs $g \mapsto (\mathrm{dualWhittakerFn3}\,W_3)(\iota g)$ and $g \mapsto \delta(g)\,w_2(w_{0,p}\,{}^tg^{-1})$ equals $q^{m^\vee s}\,P^\vee(q^{-s})$;
--
--   (v) for every $s \in \mathbb{C}$, without any half-plane restriction, the identity of rational functions
--   $$q^{m^\vee s}P^\vee(q^{-s}) = \big(C_0 q^{-k_0 s}\big)\big(C_1 q^{-k_1 s}\big)\cdot\big(q^{-ms}P(q^{s})\big)$$
--   holds; that is, the dual Laurent polynomial at $s$ is the product of the two monomial constants $\gamma_i(-s) = C_i q^{-k_i s}$ with the primal one evaluated at $-s$.
--
--   This is the local statement at a finite place of the multiplicativity of the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg $\gamma$-factor in the second variable when the $\mathrm{GL}_2$ representation is embedded in a principal series $I(\chi_0,\chi_1)$: rationality of the two local integrals in $q^{-s}$ together with a functional equation whose constant is the product of the two twisted $\mathrm{GL}_3\times\mathrm{GL}_1$ constants supplied by `h31`. It feeds the global converse-theorem input of the Langlands–Tunnell branch, being used by [`LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global`](thm.html#LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (C : Fin 2 → ℂ) (k : Fin 2 → ℤ)
    (h31 : ∀ i : Fin 2,
      ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base (χ i) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (χ i) s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) ((χ i))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base (χ i) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C i * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k i : ℂ) * s))))

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (hPS : ∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => w (g * h)) = fun g => Φ w (g * h)) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w = 0 → w = 0) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w ∈ principalSeries2 p χ))

    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))
    (hβ : ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              ((C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
                (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by sorry
