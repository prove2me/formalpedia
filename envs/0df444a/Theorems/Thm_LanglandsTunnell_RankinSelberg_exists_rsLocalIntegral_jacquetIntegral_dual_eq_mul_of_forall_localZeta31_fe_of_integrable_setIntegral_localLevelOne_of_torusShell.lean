-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/a9208dc3-882d-5050-9840-71b6da4b65a1
-- title:
--   Local GL₃timesGL₂ functional equation for a Jacquet-integral section
-- statement:
--   Throughout, $p$ is a nonzero prime of $\mathbb{Z}$ (a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$), $F = \mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`, $q =$ `Ideal.absNorm p.asIdeal`, $\psi_p$ is the local component at $p$ of the standard additive character of the adeles of $\mathbb{Q}$, $\nu =$ `selfDualHaarAt ℚ p` is the additive Haar measure on $F$ normalised by the level of $\psi_p$, and $d^\times$ denotes the multiplicative measure `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))` on $F^\times$, i.e. the pull-back along the inclusion $F^\times \hookrightarrow F$ of $\nu$ restricted to $F \setminus \{0\}$ with density $|x|^{-1}$, where $|\cdot| =$ `modulus` is the normalised absolute value. An element $\varpi$ of the valuation ring is fixed whose image in $F$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), and $b$ is a natural number. Write $\iota =$ `iotaGL` for the embedding $\mathrm{GL}_2 \to \mathrm{GL}_3$, $h \mapsto \mathrm{diag}(h,1)$, write $w_3 =$ `longWeyl3` for the antidiagonal permutation matrix of size $3$, $w' =$ `weylPrime3` for the permutation matrix interchanging the last two coordinates, ${}^t g^{-1}$ for `transposeInv3` and [`AutomorphicForm.transposeInvN (Fin 2)`](def/AutomorphicForm_SmoothingKernel.html#L28), and $K_b =$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178) for the subgroup of $\mathrm{GL}_2(F)$ that is the preimage, under the embedding of $\mathrm{GL}_2(F)$ into $\mathrm{GL}_2$ of the finite adeles placing the matrix at $p$ and the identity elsewhere, of the subgroup `finiteLevelOne` of level $\mathfrak{p}^b$ (those $g$ with $g$ and $g^{-1}$ both satisfying `IsLevelOneMatrix` for that ideal).
--
--   The $\mathrm{GL}_3$ data consist of a function $W_3 =$ `W₃base` on $\mathrm{GL}_3(F)$ subject to four hypotheses: `hW₃law`, that $W_3(n(x,y,z)h) = \psi_p^{-1}(x+y)\,W_3(h)$ for all $x,y,z \in F$ and $h$, where $n(x,y,z) =$ `upperUnipotent3 x y z`; `hW₃sm`, that there is an open subgroup $U_v$ of $\mathrm{GL}_3(F)$ with $W_3(hk) = W_3(h)$ for all $k \in U_v$; `hω₃`, that $W_3(t\cdot I_3 \cdot h) = \omega_3(t) W_3(h)$ for a character $\omega_3 : F^\times \to \mathbb{C}^\times$ and all $t, h$; and the gauge bound `hWgauge`, that there are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, with $A_1(h) = \mathrm{detSize}(h)\,\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $A_2(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ (formed from $\|\det h\|$, the supremum of the norms of the entries of the last row, and the supremum of the norms of the three $2\times 2$ minors built from the last two rows), one has $W_3(h) = 0$ unless $A_1(h) \le B$ and $A_2(h) \le B$, and $\|W_3(h)\| \le C/(A_1(h)A_2(h))^t$ when both bounds hold. An element $g_3 \in \mathrm{GL}_3(F)$ is fixed.
--
--   The torus-shell vanishing hypothesis `hβ` requires: for every $k_0 \in \mathrm{GL}_2(F)$, every character $\eta$ of $F^\times$ having conductor exponent $c$ at $p$ in the sense of `HasConductorExponentAt` (i.e. $\eta$ is trivial on `higherUnitsAt ℚ p c` and nontrivial on `higherUnitsAt ℚ p m` for each $m < c$) with $c \le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, there is a finite set $T \subseteq \mathbb{Z} \times \mathbb{Z}$ such that for all $(n_1,n_2) \notin T$ both of the following vanish: the integral over $\{u \in F^\times : |u| = 1\}$, against $d^\times$, of $\eta(u)$ times $\int_{K_b} W_3\bigl(\iota(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,(k_0k))\,g_3\bigr)\,d\mu_2(k)$, and the same integral with the integrand replaced by $W_3\bigl(w_3\,{}^t\iota(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,(k_0\,{}^tk^{-1}))^{-1}\,g_3\bigr)$, that is with `dualWhittakerFn3` of $x \mapsto W_3(xg_3)$ in place of $W_3(\,\cdot\,g_3)$ and $k$ replaced by ${}^tk^{-1}$.
--
--   The $\mathrm{GL}_2$ data consist of a pair of characters $\chi_0, \chi_1$ of $F^\times$ (written $\chi : \mathrm{Fin}\,2 \to \mathrm{Hom}(F^\times,\mathbb{C}^\times)$) with `hχb`: each $\chi_i$ is trivial on `higherUnitsAt ℚ p b`, namely on the units $u$ with $|u| = 1$ and, when $b > 0$, $|u-1| \le \exp(-b)$; constants $C_0, C_1 \in \mathbb{C}$ and integers $k_0, k_1$; a function $f$ on $\mathrm{GL}_2(F)$ lying in `principalSeries2 p χ` (`hf`), i.e. $f$ is locally constant, left invariant under $\mathrm{upperUnipotent2}$, and $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\sqrt{|a_0|/|a_1|}\,f(g)$; the right invariance `hfK` of $f$ under $K_b$; and an element $w_0 \in \mathrm{GL}_2(F)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`).
--
--   The functional-equation hypothesis `h31` requires, for each $i \in \{0,1\}$ and each $g \in \mathrm{GL}_3(F)$, the existence of polynomials $Q_1, Q_2 \in \mathbb{C}[X]$ with $Q_2 \neq 0$, an integer $n$ and reals $\sigma_0, \sigma_1$ such that: (a) for $\mathrm{Re}\,s > \sigma_0$ the function $a \mapsto W_3(\iota(\mathrm{diag}(a,1))g)\chi_i(a)|a|^{s-1}$ is $d^\times$-integrable; (b) for $\mathrm{Re}\,s > \sigma_0$, $\ \mathrm{localZeta30}(s,g) \cdot Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ns}$, where $\mathrm{localZeta30}(s,g) = \int_{F^\times} W_3(\iota(\mathrm{diag}(a,1))g)\chi_i(a)|a|^{s-1}\,d^\times a$; (c) for $\mathrm{Re}\,s > \sigma_1$ the function $(a,x) \mapsto \widetilde{W_3}(\iota(\mathrm{diag}(a,1))\,u^-(x)\,(w'\,{}^tg^{-1}))\,\chi_i^{-1}(a)|a|^{s-1}$ is integrable on $F^\times \times F$ for $d^\times \times \nu$, where $\widetilde{W_3} =$ `dualWhittakerFn3 W₃base` and $u^-(x) =$ `lowerUnipotent21 x`; and (d) for every $s$ with $\sigma_1 < \mathrm{Re}(1-s)$,
--   $$\mathrm{localZetaDual31}(1-s,g)\cdot Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ns}\cdot\bigl(C_i\,q^{k_i s}\bigr),$$
--   where $\mathrm{localZetaDual31}(1-s,g) = \int_{F^\times}\bigl(\int_F \widetilde{W_3}(\iota(\mathrm{diag}(a,1))u^-(x)(w'\,{}^tg^{-1}))\,d\nu(x)\bigr)\chi_i^{-1}(a)|a|^{-s}\,d^\times a$.
--
--   Under these hypotheses the conclusion is asserted for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ (with the Borel structure coming from the topology) and every Haar measure $\mu_{N}$ on the subgroup $N =$ range of `unipotentGL2Hom`, the upper unipotent subgroup $\{u(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}\}$, and it is conditional on three further integrability premises. The first premise asks for some $\sigma_P$ with: for all $s$ with $\mathrm{Re}\,s > \sigma_P$, $g \mapsto W_3(\iota(g)g_3)f(w_0g)\,|\det g|^{s-1/2}$ is $\mu_2$-integrable. The second asks for some $\sigma_D$ with: for all $s$ with $\mathrm{Re}\,s > \sigma_D$, $g \mapsto \widetilde{W_3^{g_3}}(\iota(g))\cdot\bigl(|\det(w_0g)|\,f(w_0\,{}^t(w_0g)^{-1})\bigr)\,|\det g|^{s-1/2}$ is $\mu_2$-integrable, where $\widetilde{W_3^{g_3}}(h) = W_3(w_3\,{}^th^{-1}g_3)$. The third asks for reals $\sigma_a < \sigma_b$ such that for all $s$ in the strip $\sigma_a < \mathrm{Re}\,s < \sigma_b$ the following two functions of $(y,(a,t)) \in F \times (F^\times \times F^\times)$ are integrable for $\nu \times (d^\times \times d^\times)$: first,
--   $$f(w_0\,u(y))\cdot\Bigl(\chi_1(a)^{-1}\omega_3(a)^{-1}|a|^{s}\,\chi_0(t)|t|^{-s-1}\int_{K_b} W_3\bigl(\iota(\mathrm{diag}(ta,a))\,(w_3\,n(0,0,y)\,w')\,\iota(k)\,g_3\bigr)d\mu_2(k)\Bigr),$$
--   and second the same expression with $f(w_0u(y))$ replaced by $f\bigl(w_0\,{}^t(w_0\,u(y))^{-1}\bigr)$ and with $w_3\,n(0,0,y)\,w'$ replaced by $w_3\,n(0,0,-y)\,w_3\,w'$ (here `upperUnipotent2 p y` is the $\mathrm{GL}_2$ matrix $u(y)$ and `diagUnits2 (t*a) a` is $\mathrm{diag}(ta,a)$).
--
--   The conclusion is the existence of polynomials $P, P^{\vee} \in \mathbb{C}[X]$, integers $m, m^{\vee}$ and reals $\sigma_2, \sigma_3$ such that the following five assertions hold, all integrals over $\mathrm{GL}_2(F)$ being taken against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to $N$ and $\mu_{N}$ (the normalised weight used to realise integration over $N\backslash\mathrm{GL}_2(F)$), and $J f(g) = \int_F f(w_0u(y)g)\,\psi_p^{-1}(y)\,d\nu(y)$ denoting the Jacquet integral:
--
--   (1) for every $s$ with $\mathrm{Re}\,s > \sigma_2$, the function $g \mapsto \bigl(W_3(\iota(g)g_3)\cdot Jf(g)\bigr)|\det g|^{s-1/2}$ is integrable for that weighted measure;
--
--   (2) for every $s$ with $\mathrm{Re}\,s > \sigma_3$, the function $g \mapsto \bigl(\widetilde{W_3^{g_3}}(\iota(g))\cdot\bigl(|\det g|\cdot\int_F f\bigl(w_0u(y)\,(w_0\,{}^tg^{-1})\bigr)\psi_p^{-1}(y)\,d\nu(y)\bigr)\bigr)|\det g|^{s-1/2}$ is integrable for that weighted measure;
--
--   (3) for every $s$ with $\mathrm{Re}\,s > \sigma_2$, the Rankin–Selberg local integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) with modulus $\delta(g) = |\det g|$, Whittaker factor $g \mapsto W_3(\iota(g)g_3)$ and section factor $g \mapsto Jf(g)$, namely $\int \bigl(W_3(\iota(g)g_3)Jf(g)\bigr)|\det g|^{s-1/2}$, equals $q^{ms}P(q^{-s})$;
--
--   (4) for every $s$ with $\mathrm{Re}\,s > \sigma_3$, the same local integral with Whittaker factor $g \mapsto \widetilde{W_3^{g_3}}(\iota(g))$ and section factor $g \mapsto |\det g|\int_F f\bigl(w_0u(y)(w_0\,{}^tg^{-1})\bigr)\psi_p^{-1}(y)\,d\nu(y)$ equals $q^{m^{\vee}s}P^{\vee}(q^{-s})$;
--
--   (5) for every $s \in \mathbb{C}$ (an identity of the resulting exponential polynomials, with no convergence restriction),
--   $$q^{m^{\vee}s}P^{\vee}(q^{-s}) = \bigl(C_0\,q^{-k_0 s}\bigr)\bigl(C_1\,q^{-k_1 s}\bigr)\cdot\bigl(q^{-ms}P(q^{s})\bigr).$$
--   Thus the constant relating the dual local integral to the original one is exactly the product of the two $\mathrm{GL}_3\times\mathrm{GL}_1$ constants $C_i q^{-k_i s}$ supplied by `h31`.
--
--   This is the local multiplicativity step for the $\mathrm{GL}_3\times\mathrm{GL}_2$ gamma factor in the $\mathrm{GL}_2$ variable, in the form used for a single principal-series section in its range of absolute convergence: the local Rankin–Selberg integral of the pair $(W_3(\iota(\cdot)g_3), Jf)$ and its dual are exponential polynomials in $q^{-s}$ whose ratio is the product of the two $\mathrm{GL}_3\times\mathrm{GL}_1$ functional-equation constants. It feeds the span-level version [`LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2`](thm.html#LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2), used in the cubic-induction construction of the $\mathrm{GL}_3$ automorphic form attached to an octahedral or tetrahedral representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (g₃ : LocalGL3 p)

    (hβ : ∀ (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
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

    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχb : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, χ i u = 1)
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
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) ((χ i))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base (χ i) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C i * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k i : ℂ) * s))))

    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (hfK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      f (g * k) = f g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      (∃ σP : ℝ, ∀ s : ℂ, σP < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (W₃base (iotaGL g * g₃) * f (w₀p * g)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂) →

      (∃ σD : ℝ, ∀ s : ℂ, σD < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g) *
              (((modulus ((Matrix.GeneralLinearGroup.det (w₀p * g) : (p.adicCompletion ℚ)ˣ) :
                  p.adicCompletion ℚ) : ℝ) : ℂ) *
                f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * g)))) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂) →

      (∃ σa σb : ℝ, σa < σb ∧ ∀ s : ℂ, σa < s.re → s.re < σb →
        Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
          f (w₀p * upperUnipotent2 p yat.1) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω₃ yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
              W₃base (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
                (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3) * iotaGL k * g₃) ∂μ₂))
          ((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) ∧
        Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
          f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p yat.1)) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω₃ yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
              W₃base (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
                (longWeyl3 * upperUnipotent3 0 0 (-yat.1) * longWeyl3 * weylPrime3) * iotaGL k * g₃) ∂μ₂))
          ((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →

      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W₃base (iotaGL g * g₃) *
                (∫ y, f (w₀p * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y
                  ∂(selfDualHaarAt ℚ p))) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g) *
                (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
                  ∫ y, f (w₀p * unipotentGL2 y * (w₀p * AutomorphicForm.transposeInvN (Fin 2) g)) *
                    (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y ∂(selfDualHaarAt ℚ p))) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => W₃base (iotaGL g * g₃))
              (fun g => ∫ y, f (w₀p * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y
                ∂(selfDualHaarAt ℚ p)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g))
              (fun g => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                  p.adicCompletion ℚ) : ℝ) : ℂ) *
                ∫ y, f (w₀p * unipotentGL2 y * (w₀p * AutomorphicForm.transposeInvN (Fin 2) g)) *
                  (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y ∂(selfDualHaarAt ℚ p)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            ((C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
              (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by sorry
