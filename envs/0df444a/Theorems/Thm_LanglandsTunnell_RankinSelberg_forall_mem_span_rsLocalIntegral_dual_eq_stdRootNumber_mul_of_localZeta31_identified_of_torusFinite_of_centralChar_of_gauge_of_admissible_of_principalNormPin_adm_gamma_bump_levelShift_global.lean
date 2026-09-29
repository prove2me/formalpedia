-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/f0918550-5c61-5cca-aca7-1e1fcf915dd1
-- title:
--   Value form of the local GL₂timesGL₃ functional equation at p
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$, equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ that is integral, an idele character $\mu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ satisfying `IsAdmissibleTwist K μ` (trivial on the principal ideles coming from $K^\times$, continuous and unitary), and a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$; write $\mathbb{Q}_p$ for `p.adicCompletion ℚ` and $\mathrm{N}p$ for `Ideal.absNorm p.asIdeal`. The hypothesis `_hdeg` records $\operatorname{finrank}_{\mathbb{Q}} K = 3$.
--
--   *Data on the $\mathrm{GL}_3$ side.* An admissible twist $\chi_A$ of $\mathbb{Q}$ together with an integer $k_p$ such that `localChar χA p` has conductor exponent exactly $k_p$ (`HasConductorExponentAt`: trivial on the $k_p$-th higher unit group and, for every $m < k_p$, non-trivial on the $m$-th). A function $W_{3,\mathrm{base}}$ on $\mathrm{GL}_3(\mathbb{Q}_p)$ which is: a $\psi_p^{-1}$-Whittaker function, i.e. $W_{3,\mathrm{base}}(u(x,y,z)g) = \psi_p(x+y)^{-1}W_{3,\mathrm{base}}(g)$ for the upper unipotent matrices `upperUnipotent3 x y z` and the standard local additive character $\psi_p =$ `psiLocal ℚ p` (`hW₃law`); right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_p)$ (`hW₃sm`); non-zero (`hW₃ne`); an eigenvector for the centre with unitary eigencharacter $\omega_3$ of $\mathbb{Q}_p^\times$ (`hω₃`, `hω₃u`). Furthermore `hW₃irr` asserts that every non-zero element $W$ of `gl3CyclicSubspace W₃base` (the $\mathbb{C}$-span of the right translates of $W_{3,\mathrm{base}}$) has $W_{3,\mathrm{base}}$ in its own cyclic span, and `hW₃adm` that for every open subgroup $U_v$ there is a finite set of functions whose span contains all $U_v$-right-invariant members of that cyclic span. The gauge hypothesis `hWgauge` provides $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, with `detSize h` $= \lVert \det h\rVert$, `lastRowSup h` the maximum of the norms of the entries of the last row and `minorSup h` the maximum of the norms of the three $2\times 2$ minors formed from the last two rows, $W_{3,\mathrm{base}}(h) = 0$ unless both $\mathrm{detSize}(h)\,\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2 \le B$ and $\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2 \le B$, and in the latter case $\lVert W_{3,\mathrm{base}}(h)\rVert$ is bounded by $C$ divided by the $t$-th power of the product of these two quantities. A level hypothesis `hπ₀lev` for an integer $d$ gives a non-zero $W'$ in the cyclic span such that $g \mapsto \chi_{A,p}(\det g)^{-1}W'(g)$ is right invariant under those $k$ in `localMaximalCompact3 (𝓞 ℚ) ℚ p` (entries of $k$ and of $k^{-1}$ of valuation $\le 1$) with $v(k_{ij}-\delta_{ij}) \le \exp(-d)$ for all $i,j$.
--
--   *Identification of the $\mathrm{GL}_3\times\mathrm{GL}_1$ local constants.* For a complex number $\mathrm{lam}$, `hId` states: for every $b \in \mathbb{N}$ such that $2e(w/p)b + 1 \le$ `conductorExponentAt K w (localChar μ w)` for all $w$ in `primeFibre ℚ K p` (the primes of $\mathcal{O}_K$ lying under $p$), for every character $\eta$ of $\mathbb{Q}_p^\times$ with conductor exponent $c_\eta \le b$ arising as `localChar ηA p` for an admissible twist $\eta_A$ of $\mathbb{Q}$ whose base change $\eta_A \circ$ `(genuineBaseChange ℚ K).idelicNorm` is an admissible twist of $K$, and for every $g \in \mathrm{GL}_3(\mathbb{Q}_p)$, there are polynomials $Q_1, Q_2$ with $Q_2 \ne 0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that: the $(3,0)$ integral `localZeta30` of $W_{3,\mathrm{base}}$ against $\eta$ at $g$ converges absolutely for $\operatorname{Re} s > \sigma_0$ and satisfies $\mathrm{localZeta30}(s)\,Q_2(\mathrm{N}p^{-s}) = Q_1(\mathrm{N}p^{-s})\,\mathrm{N}p^{ns}$ there; the dual $(3,1)$ integrand for `dualWhittakerFn3 W₃base`, $\eta^{-1}$ and the point `weylPrime3 * transposeInv3 g` is integrable for $\operatorname{Re} s > \sigma_1$; and for all $s$ with $\sigma_1 < \operatorname{Re}(1-s)$,
--   $$\mathrm{localZetaDual31}(1-s)\,Q_2(\mathrm{N}p^{-s}) = Q_1(\mathrm{N}p^{-s})\,\mathrm{N}p^{ns}\cdot\Big(\mathrm{lam}\cdot\prod_{w \mid p}(\eta_A\!\circ\! N\cdot\mu)_w(-1)\cdot\prod_{w\mid p}\varepsilon\big((\eta_A\!\circ\! N\cdot\mu)_w\big)\,\big(\mathrm{N}w^{1/2-s}\big)^{\mathrm{pinnedExp}(\eta_A\circ N\cdot\mu, w)}\Big),$$
--   where $\varepsilon$ is `stdRootNumberAt`, $\mathrm{pinnedExp}(\cdot,w)$ is the conductor exponent plus `addCharLevel (psiLocal K w)`, the products are `finprod`s over `primeFibre ℚ K p`, and all integrals are taken against the multiplicative measure on $\mathbb{Q}_p^\times$ obtained from `mulMeasure (selfDualHaarAt ℚ p)` by comap along `Units.val`, with `selfDualHaarAt ℚ p` on $\mathbb{Q}_p$ in the $(3,1)$ variable.
--
--   *Data on the $\mathrm{GL}_2$ side and the level.* An ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$ with $N \ne \bot$ (`_hN`), satisfying the floor condition `hfloor`: for every $w \mid p$, $4\big(\mathrm{count}_w(N\mathcal{O}_K) + \mathrm{addCharLevel}(\psi_w)+1\big) \le$ `conductorExponentAt K w (localChar μ w)`. A function $w_{2,\mathrm{base}}$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ which is $\psi_p$-Whittaker for the unipotent matrices `unipotent x` (`hw₂law`), right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage of the finite adelic level-one subgroup of level $N$ under the local embedding at $p$) (`hw₂K`), non-zero (`hw₂ne`), with irreducible cyclic span in the same sense as above (`hw₂irr`) and admissible finite spanning sets for right invariants under open subgroups (`hw₂adm`). An admissible twist $\eta_A$ of $\mathbb{Q}$ whose base change along the genuine idelic norm is an admissible twist of $K$ (`hηA`, `hηAN`), which is the central character of $w_{2,\mathrm{base}}$ in the sense that $w_{2,\mathrm{base}}(zI\cdot g) = (\mathrm{localChar}\,\eta_A\,p)(z)\,w_{2,\mathrm{base}}(g)$ (`hcentral`). An integer $b$ with $p^b \mid N$ and $p^{b+1}\nmid N$ (`hNb`), and the numerical conditions $6(b+3d+3)+7 \le k_p$ (`hkC`) and, for an integer $\Delta$, $6d+18+\Delta \le k_p$ (`hΔ`).
--
--   *Bump functions.* `hbumpAll` states: for every admissible twist $\xi_A$ of $\mathbb{Q}$ that is unramified at all finite places $v \ne p$ and has archimedean component of type $(0,0)$ at every real place (`IsArchCompAt ℚ ξA v 0 0`), and every $B \in \mathbb{N}$ with $2d+6 \le B$ such that `localChar ξA p` has conductor exponent $B$, there is $W_0$ in the cyclic span of $g \mapsto \xi_{A,p}(\det g)\,\chi_{A,p}(\det g)^{-1}W_{3,\mathrm{base}}(g)$ which is right invariant under `congruenceK1 (𝓞 ℚ) ℚ p (3*B + Δ)` (the $k$ in `localMaximalCompact3` whose bottom row is congruent to $(0,0,1)$ at level $3B+\Delta$), whose restriction along `iotaGL` is right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), which vanishes at `iotaGL h` unless $h =$ `unipotentGL2 x` times an element of that same subgroup, and which takes the value $1$ at `iotaGL 1`.
--
--   *Uniformiser, growth, cell vanishing, Weyl element, $\gamma$-factor.* An element $\varpi$ of the valuation ring with non-zero image and valuation $\exp(-1)$ (`hπ`, `hϖ`). `hw₂gr`: there are $C, A \in \mathbb{R}$ with $\lVert w_{2,\mathrm{base}}(\mathrm{diagZ}(\varpi,m)\,k)\rVert \le C\,(\mathrm{N}p)^{Am}$ for all $m \ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178). `hβ`: for every $g_3 \in \mathrm{GL}_3(\mathbb{Q}_p)$, $k_0 \in \mathrm{GL}_2(\mathbb{Q}_p)$, character $\eta$ of $\mathbb{Q}_p^\times$ of conductor exponent $c \le b$ and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$, there is a finite set $T \subset \mathbb{Z}\times\mathbb{Z}$ such that for $n \notin T$ both of the following cell integrals vanish: the integral over $\{u : v(u)=1\}$, against the multiplicative measure, of $\eta(u)$ times the $\mu_2$-integral over [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178) of $W_{3,\mathrm{base}}\big(\mathrm{iotaGL}(\mathrm{scalarPi}(\varpi)^{n_2}\,\mathrm{diagUnitGL2}(\varpi^{n_1}u)\,(k_0k))\,g_3\big)$, and the same expression with $W_{3,\mathrm{base}}$ replaced by `dualWhittakerFn3 (fun x => W₃base (x * g₃))` and $k$ replaced by `transposeInvN (Fin 2) k`. An element $w_{0p}$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ whose matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`). Finally `hΓ` posits polynomials $R_1, R_2$ with $R_2 \ne 0$ and an integer $r$ such that, for all Haar measures $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ and $\mu_{N_2}$ on the range of `unipotentGL2Hom`, all $w_2$ in the cyclic span of $w_{2,\mathrm{base}}$, all $W_3$ in the cyclic span of $W_{3,\mathrm{base}}$, and all $P, P_d, Q, Q_d$ with $Q, Q_d \ne 0$, $m, m_d \in \mathbb{Z}$ and $\sigma_2,\sigma_3 \in \mathbb{R}$: if the two integrability statements and the two rationality statements listed in the conclusion below hold (with $Q$, $Q_d$ inserted as the denominators), then for all $s$
--   $$R_2(\mathrm{N}p^{s})\,\mathrm{N}p^{m_d s}P_d(\mathrm{N}p^{-s})\,Q(\mathrm{N}p^{s}) = R_1(\mathrm{N}p^{s})\,\mathrm{N}p^{rs}\cdot \mathrm{N}p^{-ms}P(\mathrm{N}p^{s})\cdot Q_d(\mathrm{N}p^{-s}).$$
--
--   *Conclusion.* For every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ (with the Borel structure `localGLBorel ℚ p`), every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, every $w_2$ in the $\mathbb{C}$-span of the right translates of $w_{2,\mathrm{base}}$ and every $W_3$ in `gl3CyclicSubspace W₃base`, there exist polynomials $P, P_d \in \mathbb{C}[X]$, integers $m, m_d$ and reals $\sigma_2,\sigma_3$ such that the following five assertions hold, all integrals being taken against $\mu_2$ weighted by the Haar quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$, and $\delta(g) = \mathrm{modulus}(\det g)$.
--
--   First, for $\operatorname{Re} s > \sigma_2$ the function $g \mapsto W_3(\mathrm{iotaGL}\,g)\,w_2(g)\,\delta(g)^{s-1/2}$ is integrable. Secondly, for $\operatorname{Re} s > \sigma_3$ the function $g \mapsto \mathrm{dualWhittakerFn3}(W_3)(\mathrm{iotaGL}\,g)\cdot \delta(g)\,w_2(w_{0p}\,\mathrm{transposeInvN}(g))\cdot\delta(g)^{s-1/2}$ is integrable. Thirdly, for $\operatorname{Re} s > \sigma_2$,
--   $$\mathrm{rsLocalIntegral}\big(s; W_3\circ\mathrm{iotaGL},\,w_2\big) = \mathrm{N}p^{ms}\,P(\mathrm{N}p^{-s}).$$
--   Fourthly, for $\operatorname{Re} s > \sigma_3$,
--   $$\mathrm{rsLocalIntegral}\big(s;\ \mathrm{dualWhittakerFn3}(W_3)\circ\mathrm{iotaGL},\ g\mapsto \delta(g)\,w_2(w_{0p}\,\mathrm{transposeInvN}(g))\big) = \mathrm{N}p^{m_d s}\,P_d(\mathrm{N}p^{-s}).$$
--   Fifthly, for every $s \in \mathbb{C}$,
--   $$\mathrm{N}p^{m_d s}P_d(\mathrm{N}p^{-s}) = \mathrm{lam}^2\cdot\Big(\prod_{w\mid p}(\eta_A\!\circ\! N\cdot\mu)_w(-1)\cdot\prod_{w\mid p}\mu_w(-1)\Big)\cdot\Big(\prod_{w\mid p}\varepsilon\big((\eta_A\!\circ\! N\cdot\mu)_w\big)\big(\mathrm{N}w^{1/2+s}\big)^{\mathrm{pinnedExp}(\eta_A\circ N\cdot\mu,w)}\cdot\prod_{w\mid p}\varepsilon(\mu_w)\big(\mathrm{N}w^{1/2+s}\big)^{\mathrm{pinnedExp}(\mu,w)}\Big)\cdot \mathrm{N}p^{-ms}P(\mathrm{N}p^{s}),$$
--   where again $\varepsilon =$ `stdRootNumberAt K w`, the characters indexed by $w$ are the local components `localChar · w`, and the products are `finprod`s over `primeFibre ℚ K p`.
--
--   Thus the two local Rankin–Selberg integrals are, on their half-planes of convergence, Laurent-polynomial expressions in $\mathrm{N}p^{-s}$, and the dual expression is obtained from the first by the substitution $s \mapsto 1-s$ up to the explicit constant built from $\mathrm{lam}^2$, the values at $-1$ and the root numbers of $\mu$ and of its twist by the base change of $\eta_A$.
--
--   This is the value form of the local functional equation for the $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg integrals at a finite place $p$: the existence form supplies a $\gamma$-factor as a hypothesis, and the local constants of the $\mathrm{GL}_3$ datum twisted by characters of small conductor are priced by root numbers attached to the cubic field $K$ and the character $\mu$. It feeds the converse-theorem input of the cubic-induction (Langlands–Tunnell) part of the development, being used in the assembly of global cell sums for the Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_stdRootNumber_mul_of_localZeta31_identified_of_torusFinite_of_centralChar_of_gauge_of_admissible_of_principalNormPin_adm_gamma_bump_levelShift_global
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : LanglandsTunnell.Converse.IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ))

    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (kp : ℕ)
    (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) kp)

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)

    (hω₃u : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω₃ x : ℂˣ) : ℂ)‖ = 1)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (d : ℕ)
    (hπ₀lev : ∃ W' ∈ gl3CyclicSubspace W₃base, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)

    (lam : ℂ)
    (hId :
      ∀ b : ℕ,
              (∀ w ∈ primeFibre ℚ K p,
            2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
              LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
          ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
            LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
            ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
              NumberField.TateGlobal.localChar ηA p = η →
              LanglandsTunnell.Converse.IsAdmissibleTwist K
                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
              ∀ g : LocalGL3 p,
                letI := localBorel ℚ p
                ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                  IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
                    W₃base η g σ₀ ∧
                  (∀ s : ℂ, σ₀ < s.re →
                    localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
                      Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                  IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                  (∀ s : ℂ, σ₁ < (1 - s).re →
                    localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                      W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                      (lam *
                        (∏ᶠ w ∈ primeFibre ℚ K p,
                          ((NumberField.TateGlobal.localChar
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                        (∏ᶠ w ∈ primeFibre ℚ K p,
                          (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                              (NumberField.TateGlobal.localChar
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                              (LanglandsTunnell.Converse.pinnedExp K
                                  (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      4 * (FractionalIdeal.count K w
            ((N.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hηA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA)
    (hηAN : LanglandsTunnell.Converse.IsAdmissibleTwist K
      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
        ((NumberField.TateGlobal.localChar ηA p z : ℂˣ) : ℂ) * w₂base g)

    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)

    (hkC : 6 * (b + 3 * d + 3) + 7 ≤ kp)

    (Δ : ℕ) (hΔ : 6 * d + 18 + Δ ≤ kp)

    (hbumpAll : ∀ (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → NumberField.TateGlobal.IsUnramifiedCharAt ξA v) →
      (∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0) →
      ∀ B : ℕ, 2 * d + 6 ≤ B → LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B →
      ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
          ((NumberField.TateGlobal.localChar ξA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W₃base g),
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ), ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
        (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
          W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
          ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
        W₀ (iotaGL 1) = 1)
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
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (hΓ :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) :
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
              (lam ^ 2 *
                ((∏ᶠ w ∈ primeFibre ℚ K p,
                    ((NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                  ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)) *
                ((∏ᶠ w ∈ primeFibre ℚ K p,
                    (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                      (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + s)) ^
                        (LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) *
                  ∏ᶠ w ∈ primeFibre ℚ K p,
                    (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar μ w) *
                      (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 + s)) ^
                        (LanglandsTunnell.Converse.pinnedExp K μ w)))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by sorry
