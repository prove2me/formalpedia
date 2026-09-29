-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_and_dual_integrable_and_eq_rational_sphericalWhittaker_of_forall_localZeta31_fe_of_gauge
-- name    : LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_and_dual_integrable_and_eq_rational_sphericalWhittaker_of_forall_localZeta31_fe_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b6b83a33-35dc-5357-99cd-0f427a3fceeb
-- title:
--   Convergence and rationality of local GL₃× GL₂ Rankin–Selberg integrals
-- statement:
--   Throughout, $v$ is a nonzero prime of the ring of integers of $\mathbb Q$, $N_v =$ `Ideal.absNorm v.asIdeal` is the absolute norm of the corresponding prime ideal, $\mathbb Q_v$ denotes the completion `v.adicCompletion ℚ`, and `LocalGL3 v` is $GL_3(\mathbb Q_v)$.
--
--   The data on the $GL_3$ side are: an additive character $\psi_v$ of $\mathbb Q_v$, assumed by `hψinv` to be the inverse of the standard local character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65); a function $W : GL_3(\mathbb Q_v) \to \mathbb C$; a character $\omega_v : \mathbb Q_v^{\times} \to \mathbb C^{\times}$; an element $\varpi$ of the valuation ring of $\mathbb Q_v$ whose image in $\mathbb Q_v$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), i.e. a uniformiser; polynomials $E, E^{\vee} \in \mathbb C[X]$, a scalar $\varepsilon \in \mathbb C$ and a natural number $\ell$.
--
--   The hypotheses on $W$ are the following. `hW` is the predicate `IsGL3PsiWhittakerFn ψv W`: for all $x,y,z \in \mathbb Q_v$ and all $g$, $W(u(x,y,z)\,g) = \psi_v(x+y)\,W(g)$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$ in position $(0,1)$, $y$ in $(1,2)$ and $z$ in $(0,2)$. `hW1` normalises $W(1)=1$. `hmult` is `HasWhittakerMultOne ψv W`, i.e. the $\mathbb C$-module `gl3WhittakerFunctionalSpace` attached to the cyclic representation `gl3CyclicRep W` and to $\psi_v$ has rank at most $1$; here `gl3CyclicSubspace W` is the $\mathbb C$-span of the right translates $h' \mapsto W(h'h)$ of $W$ inside the space of all functions $GL_3(\mathbb Q_v) \to \mathbb C$, and `gl3CyclicRep W` is the right-translation action of $GL_3(\mathbb Q_v)$ on it. `hirr` is an irreducibility condition: every nonzero $F$ in `gl3CyclicSubspace W` has $W$ in `gl3CyclicSubspace F`. `hsm` is smoothness: some open subgroup $U_v \le GL_3(\mathbb Q_v)$ satisfies $W(gk)=W(g)$ for all $k \in U_v$ and all $g$. `hadm` is admissibility: for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $F \in$ `gl3CyclicSubspace W` which is right $U_v$-invariant lies in the $\mathbb C$-span of $B$. `hωu` asserts that $\omega_v$ is unitary, $\|\omega_v(z)\| = 1$ for all $z$, and `hω` that $\omega_v$ is the central character of $W$: $W(\mathrm{diag}(t,t,t)\,h) = \omega_v(t) W(h)$.
--
--   The hypothesis `hWgauge` is the two-parameter gauge majorisation. Writing, for $h \in GL_3(\mathbb Q_v)$,
--   $$X(h) = \frac{\mathrm{detSize}(h)\cdot \mathrm{lastRowSup}(h)}{\mathrm{minorSup}(h)^2}, \qquad Y(h) = \frac{\mathrm{minorSup}(h)}{\mathrm{lastRowSup}(h)^2},$$
--   where `detSize h` $=\|\det h\|$, `lastRowSup h` is the maximum of the norms of the three entries of the bottom row of $h$, and `minorSup h` is the maximum of the norms of the three $2\times 2$ minors $h_{1j}h_{2j'} - h_{1j'}h_{2j}$ taken from the last two rows, the hypothesis provides $B \in \mathbb R$, $t \in \mathbb N$ and $C \in \mathbb R$ such that for every $h$: if not both $X(h) \le B$ and $Y(h) \le B$ then $W(h) = 0$; and if both $X(h) \le B$ and $Y(h) \le B$ then $\|W(h)\| \le C/(X(h)\,Y(h))^{t}$.
--
--   The hypothesis `h31` is the $GL_3 \times GL_1$ functional equation at the trivial character $1 : \mathbb Q_v^{\times} \to \mathbb C^{\times}$, with the data $(E, E^{\vee}, \varepsilon, \ell)$ common to all translates: for every $g \in GL_3(\mathbb Q_v)$ there exist $P : \mathbb C \to \mathbb C$ and $\sigma_0, \sigma_1 \in \mathbb R$ such that (i) $P$ is rational in $N_v^{-s}$ up to a power of $N_v^{s}$, in the precise sense that there are $Q, R \in \mathbb C[X]$ with $R \neq 0$ and $m \in \mathbb N$ with $P(s)\,R(N_v^{-s}) = Q(N_v^{-s})\,N_v^{ms}$ for all $s$; (ii) `IsLocalZeta30ConvergentAbove` holds for $W$, the trivial character and $g$ above $\sigma_0$, i.e. for $\operatorname{Re} s > \sigma_0$ the function $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,|a|^{s-1}$ is integrable for the multiplicative measure `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))` on $\mathbb Q_v^{\times}$ obtained from the self-dual additive Haar measure; (iii) for $\operatorname{Re} s > \sigma_0$, $\mathrm{localZeta30}(s,g) = E(N_v^{-s})^{-1} P(s)$; (iv) `IsLocalZeta31ConvergentAbove` holds, for the same multiplicative measure, the additive measure `selfDualHaarAt ℚ v`, the dual function `dualWhittakerFn3 W` $= (g \mapsto W(w_3\,{}^{t}g^{-1}))$ with $w_3$ the long Weyl element, the trivial character, the point $w' \cdot {}^{t}g^{-1}$ with $w'$ the transposition of the last two coordinates, and the bound $\sigma_1$; and (v) for all $s$ with $\operatorname{Re}(1-s) > \sigma_1$,
--   $$\mathrm{localZetaDual31}(1-s, g) = E^{\vee}\bigl(N_v^{-(1-s)}\bigr)^{-1}\,\bigl(\varepsilon\, N_v^{\ell(1/2-s)}\bigr)\,P(s),$$
--   where `localZetaDual31` at $1-s$ and $g$ is by definition `localZeta31` of `dualWhittakerFn3 W` at the inverse character and the point $w'\cdot {}^{t}g^{-1}$.
--
--   Under these hypotheses the conclusion is a universally quantified statement over the $GL_2$ data. Let $a_1, a_2 \in \mathbb C$ with $a_1a_2 \neq 0$. Let $W_2 : GL_2(\mathbb Q_v) \to \mathbb C$ satisfy: `hW₂ψ`, $W_2(u(x)g) = \psi_{v}^{\mathrm{std}}(x) W_2(g)$ for the unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and the standard character; `hW₂K`, right invariance under the local level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) at the unit ideal, that is the pullback under the local embedding into $GL_2$ of the finite adeles of the finite level-one subgroup; `hW₂1`, $W_2(1)=1$; `hW₂Z`, $W_2(g\,\mathrm{diag}(\varpi,\varpi)) = (a_1a_2/N_v) W_2(g)$; and `hW₂T`, $W_2(\mathrm{diag}(\varpi^{m},1)) = \mathrm{torusFactor}(N_v, a_1+a_2, a_1a_2/N_v, m)$ for all $m \in \mathbb Z$, where `torusFactor` is given by the Hecke recursion sequence for $m \ge 0$ and vanishes for $m < 0$. Let $W_2^{d}$ satisfy the same five conditions with the inverse character $(\psi_v^{\mathrm{std}})^{-1}$ in place of $\psi_v^{\mathrm{std}}$, central eigenvalue $N_v/(a_1a_2)$, and torus values $\mathrm{torusFactor}(N_v, N_v(a_1+a_2)/(a_1a_2), N_v/(a_1a_2), m)$.
--
--   Then, $GL_2(\mathbb Q_v)$ being equipped with its Borel structure, for every Haar measure $\mu_2$ on $GL_2(\mathbb Q_v)$ and every Haar measure $\mu_N$ on the range of `unipotentGL2Hom`, the subgroup of upper unipotent matrices, there exist polynomials $p, q, p^{d}, q^{d} \in \mathbb C[X]$ and reals $\sigma_2, \sigma_3$ with $q \neq 0$ and $q^{d} \neq 0$ such that the following four assertions hold, all integrals being taken against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to the unipotent subgroup and $\mu_N$:
--
--   1. for every $s$ with $\operatorname{Re} s > \sigma_2$, the function $g \mapsto W(\iota_{GL}(g))\,W_2(g)\,|\det g|^{\,s-1/2}$ is integrable, where $\iota_{GL}$ is the embedding $GL_2 \hookrightarrow GL_3$ adjoining $1$ in the last diagonal entry and $|\cdot|$ is the module `modulus`;
--
--   2. for every $s$ with $\operatorname{Re}(1-s) > \sigma_3$, the function $g \mapsto \mathrm{dualWhittakerFn3}(W)\bigl(\iota_{GL}(g)\,\iota_{GL}(\mathrm{diag}(\varpi,\varpi)^{-\ell})\bigr)\,W_2^{d}(g)\,|\det g|^{\,1-s-1/2}$ is integrable;
--
--   3. for every $s$ with $\operatorname{Re} s > \sigma_2$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, N, \mu_N, |\det(\cdot)|, s, W \circ \iota_{GL}, W_2\bigr)\cdot q(N_v^{-s}) = p(N_v^{-s}),$$
--   where [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) denotes $\int (W(\iota_{GL}(g))\,W_2(g))\,|\det g|^{\,s-1/2}$ for the weighted measure above;
--
--   4. for every $s$ with $\operatorname{Re}(1-s) > \sigma_3$, the same integral formed at $1-s$ from the shifted dual function $g \mapsto \mathrm{dualWhittakerFn3}(W)\bigl(\iota_{GL}(g)\,\iota_{GL}(\mathrm{diag}(\varpi,\varpi)^{-\ell})\bigr)$ and from $W_2^{d}$, multiplied by $q^{d}\bigl(N_v^{-(1-s)}\bigr)$, equals $p^{d}\bigl(N_v^{-(1-s)}\bigr)$.
--
--   Thus the assertion is convergence in a right half-plane, for both the primal and the shifted dual integral, together with rationality of each integral in $N_v^{-s}$ respectively $N_v^{-(1-s)}$; no relation between the two rational functions is claimed here. The conclusion is obtained from [`LanglandsTunnell.CubicInduction.exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn`](thm.html#LanglandsTunnell.CubicInduction.exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn), whose hypotheses are the uniformiser data, the Whittaker transformation law for the inverse standard character, smoothness and admissibility of $W$, and the integer $\ell$; the remaining hypotheses above record the standing assumptions under which the citing statements invoke the result.
--
--   This is the local convergence-and-rationality half of the Jacquet–Piatetski-Shapiro–Shalika theory of $GL_3 \times GL_2$ Rankin–Selberg integrals at a finite place, in the form where the $GL_2$ factor is the normalised spherical Whittaker function with Hecke parameters $a_1, a_2$ and the $GL_3$ Whittaker function is controlled by a gauge majorisation. It feeds the two statements that combine it with the $GL_3 \times GL_1$ functional equation, namely [`LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge) and [`LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge), within the cubic-induction construction used for the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_and_dual_integrable_and_eq_rational_sphericalWhittaker_of_forall_localZeta31_fe_of_gauge.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem
LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_and_dual_integrable_and_eq_rational_sphericalWhittaker_of_forall_localZeta31_fe_of_gauge
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
        ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) := by sorry
