-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/76dd006d-1928-53d0-8ebd-b9461ef8a957
-- title:
--   Rationality of local GL₃× GL₂ Rankin–Selberg integrals and duals
-- statement:
--   Fix a non-zero prime $p$ of the ring of integers of $\mathbb{Q}$ (an element of `HeightOneSpectrum (𝓞 ℚ)`), write $F_p$ for the completion `p.adicCompletion ℚ`, $q =$ `Ideal.absNorm p.asIdeal`, and let $\psi_p =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) be the standard local additive character. `LocalGL3 p` is $GL_3(F_p)$, and `iotaGL` is the embedding $GL_2 \to GL_3$, $h \mapsto \operatorname{diag}(h,1)$ in block form.
--
--   The data on the $GL_3$ side is a function $W_{3,\mathrm{base}} : GL_3(F_p) \to \mathbb{C}$ subject to three hypotheses. `hW₃law` is the predicate `IsGL3PsiWhittakerFn` for the character $\psi_p^{-1}$: for all $x,y,z \in F_p$ and $g \in GL_3(F_p)$, $W_{3,\mathrm{base}}(u(x,y,z)g) = \psi_p^{-1}(x+y)\,W_{3,\mathrm{base}}(g)$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner. `hW₃sm` asserts the existence of an open subgroup $U_v \le GL_3(F_p)$ under which $W_{3,\mathrm{base}}$ is right invariant. `hWgauge` is the gauge majorisation: there are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, writing $a(h) = \mathrm{detSize}(h)\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $b(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ — with $\mathrm{detSize}(h) = \|\det h\|$, $\mathrm{lastRowSup}(h)$ the maximum of the norms of the three entries of the last row of $h$, and $\mathrm{minorSup}(h)$ the maximum of the norms of the three $2\times 2$ minors $h_{1j}h_{2j'} - h_{1j'}h_{2j}$ formed from the last two rows — one has $W_{3,\mathrm{base}}(h) = 0$ whenever not both $a(h) \le B$ and $b(h) \le B$, and $\|W_{3,\mathrm{base}}(h)\| \le C/(a(h)b(h))^t$ whenever $a(h) \le B$ and $b(h) \le B$.
--
--   Further data: a natural number $b$, and an element $\varpi$ of the valuation ring of $F_p$ whose image in $F_p$ is non-zero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), i.e. a uniformiser.
--
--   The hypothesis `hβrat` is the separated rationality of the torus-shell arrays. For every $g_3 \in GL_3(F_p)$, every $k_0 \in GL_2(F_p)$, every character $\eta : F_p^\times \to \mathbb{C}^\times$ and every $c \in \mathbb{N}$ such that `HasConductorExponentAt ℚ p η c` holds (that is, $\eta$ is trivial on the set of units $u$ with $|u| = 1$ and $|u-1| \le \exp(-c)$, and non-trivial on the corresponding set for each $m < c$) with $c \le b$, and for every Haar measure $\mu_2$ on $GL_2(F_p)$ for the Borel $\sigma$-algebra, define two arrays $A, A^{d} : \mathbb{Z}\times\mathbb{Z} \to \mathbb{C}$ by integration over the units $u$ of $F_p$ with $|u| = 1$, against the multiplicative measure obtained by pulling back `mulMeasure (selfDualHaarAt ℚ p)` along $u \mapsto u$, of $\eta(u)$ times the $\mu_2$-integral over $k$ in the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along the local embedding `localEmbed` of the adelic level-one subgroup `finiteLevelOne` of level $p^b$) of, respectively,
--   $$W_{3,\mathrm{base}}\bigl(\iota(\,\mathrm{diag}(\varpi,\varpi)^{n_2}\cdot \mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k\,)\cdot g_3\bigr)$$
--   and
--   $$\bigl(\mathrm{dualWhittakerFn3}\,(x \mapsto W_{3,\mathrm{base}}(xg_3))\bigr)\bigl(\iota(\,\mathrm{diag}(\varpi,\varpi)^{n_2}\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0\cdot {}^t k^{-1}\,)\bigr),$$
--   where $\iota =$ `iotaGL`, ${}^tk^{-1} =$ `transposeInvN (Fin 2) k` and $\mathrm{dualWhittakerFn3}\,W(g) = W(w_3\cdot {}^tg^{-1})$ with $w_3$ the long Weyl element `longWeyl3`. The hypothesis requires of each of $A$ and $A^{d}$, separately, the existence of $N_1 \in \mathbb{Z}$, polynomials $D_1, D_2 \in \mathbb{C}[X]$ with $D_1(0) \ne 0$ and $D_2(0) \ne 0$, and $M \in \mathbb{N}$, such that the array vanishes at every $n$ with $n_1 < N_1$ or $n_2 < N_1$, and such that for all $m_1, m_2 \in \mathbb{N}$ with $M \le m_1$ or $M \le m_2$,
--   $$\sum_{i \le \deg D_1}\ \sum_{l \le \deg D_2} D_1[i]\,D_2[l]\,A(N_1+m_1-i,\,N_1+m_2-l) = 0 .$$
--
--   The data on the $GL_2$ side is a function $w_{2,\mathrm{base}} : GL_2(F_p) \to \mathbb{C}$ with: `hw₂law`, the Whittaker law $w_{2,\mathrm{base}}(n(x)g) = \psi_p(x)\,w_{2,\mathrm{base}}(g)$ for the unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hw₂K`, right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178); a character $\omega : F_p^\times \to \mathbb{C}^\times$ and `hcentral`, the central character law $w_{2,\mathrm{base}}(z\cdot g) = \omega(z)\,w_{2,\mathrm{base}}(g)$ for scalar matrices $z$; `hw₂gr`, moderate growth along the shells: there are $C, A \in \mathbb{R}$ with $\|w_{2,\mathrm{base}}(\mathrm{diag}(\varpi^m,1)k)\| \le C\,q^{Am}$ for all $m \ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178); and `hw₂rec`, a shell recurrence: there are $N_1 \in \mathbb{Z}$, $D \in \mathbb{C}[X]$ with $D(0) \ne 0$ and $M \in \mathbb{N}$ such that for every $k$ in that same subgroup one has $w_{2,\mathrm{base}}(\mathrm{diag}(\varpi^m,1)k) = 0$ for all $m < N_1$, and $\sum_{i \le \deg D} D[i]\,w_{2,\mathrm{base}}(\mathrm{diag}(\varpi^{N_1+m-i},1)k) = 0$ for all natural $m \ge M$. Finally $w_{0,p} \in GL_2(F_p)$ is required to have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The conclusion, with the Borel $\sigma$-algebra on $GL_2(F_p)$, is: for every Haar measure $\mu_2$ on $GL_2(F_p)$, every Haar measure $\mu_{N_2}$ on the range $N_2$ of `unipotentGL2Hom` (the unipotent subgroup $\{n(x)\}$), every $w_2$ in the $\mathbb{C}$-span of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, $h \in GL_2(F_p)$, and every $W_3$ in `gl3CyclicSubspace W₃base`, the $\mathbb{C}$-span of the right translates $g \mapsto W_{3,\mathrm{base}}(gh)$, $h \in GL_3(F_p)$, there exist polynomials $P, P^d, Q, Q^d \in \mathbb{C}[X]$, integers $m, m^d$ and real numbers $\sigma_2, \sigma_3$ with $Q \ne 0$, $Q^d \ne 0$, such that the following four assertions hold, all integrals being taken against $\mu_2$ weighted by the density [`HaarQuotient.density N₂ μN₂`](def/HaarQuotient.html#L25) and $\delta(g) = \mathrm{modulus}(\det g)$ denoting the module of the determinant:
--
--   (i) for every $s$ with $\operatorname{Re} s > \sigma_2$, the function $g \mapsto W_3(\iota(g))\,w_2(g)\,\delta(g)^{s-1/2}$ is integrable;
--
--   (ii) for every $s$ with $\operatorname{Re} s > \sigma_3$, the function $g \mapsto \mathrm{dualWhittakerFn3}\,W_3(\iota(g))\cdot\bigl(\delta(g)\,w_2(w_{0,p}\,{}^tg^{-1})\bigr)\cdot\delta(g)^{s-1/2}$ is integrable;
--
--   (iii) for every $s$ with $\operatorname{Re} s > \sigma_2$,
--   $$\mathrm{rsLocalIntegral}\,\mu_2\,N_2\,\mu_{N_2}\,\delta\,s\,(W_3\circ\iota)\,w_2 \cdot Q(q^{-s}) = q^{ms}\,P(q^{-s}),$$
--   where [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) is the integral of $(W\cdot F)\,\delta^{s-1/2}$ against the weighted measure above;
--
--   (iv) for every $s$ with $\operatorname{Re} s > \sigma_3$,
--   $$\mathrm{rsLocalIntegral}\,\mu_2\,N_2\,\mu_{N_2}\,\delta\,s\,(\mathrm{dualWhittakerFn3}\,W_3\circ\iota)\,\bigl(g \mapsto \delta(g)\,w_2(w_{0,p}\,{}^tg^{-1})\bigr)\cdot Q^d(q^{-s}) = q^{m^d s}\,P^d(q^{-s}).$$
--
--   Thus the two local Rankin–Selberg integrals converge in a right half-plane and are, there, rational functions of $q^{-s}$ of the indicated shape, the integer exponents $m$, $m^d$ allowing a monomial shift.
--
--   This is the local rationality statement for the $GL_3 \times GL_2$ Rankin–Selberg convolution at a finite place, in the form needed in the cubic-induction (Langlands–Tunnell) part of the development: the Whittaker function on $GL_3$ is controlled by a gauge and has rational torus-shell arrays, while its $GL_2$ partner has a central character and recurrent Kirillov shells. It is the form in which the local integral and its $w_3$-dual are fed, through [`LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2), into the construction of the local factors of the convolution $L$-function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hβrat :
      ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
        letI := localBorel ℚ p
        letI := localGLBorel ℚ p
        haveI := borelSpace_localGLBorel ℚ p
        ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
          let A : ℤ × ℤ → ℂ := fun n =>
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          let Ad : ℤ × ℤ → ℂ := fun n =>
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
            (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
            (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
              ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
                D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) ∧
          (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
            (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Ad n = 0) ∧
            (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
              ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
                D₁.coeff i * D₂.coeff l * Ad (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)))

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)

    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))

    (hw₂rec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        (∀ m : ℤ, m < N₁ →
          w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i *
              w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0))

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

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
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
