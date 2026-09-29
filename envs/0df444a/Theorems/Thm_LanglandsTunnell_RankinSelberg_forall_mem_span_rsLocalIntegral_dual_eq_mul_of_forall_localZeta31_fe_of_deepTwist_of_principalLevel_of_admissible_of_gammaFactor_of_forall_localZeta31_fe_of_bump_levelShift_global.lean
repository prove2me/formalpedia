-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/45197b2e-bfb9-5833-b767-9f8574da09ae
-- title:
--   Pair stability of the GL₃timesGL₂ local functional equation
-- statement:
--   Throughout, $p$ is a height-one prime of $\mathcal O_{\mathbb Q}$, $\mathbb Q_p$ denotes the completion `p.adicCompletion ℚ`, $q=$ `Ideal.absNorm p.asIdeal` is the residue cardinality, and `LocalGL3 p` is $\mathrm{GL}_3(\mathbb Q_p)$. The map `iotaGL` embeds $\mathrm{GL}_2$ into $\mathrm{GL}_3$ as $h\mapsto\mathrm{diag}(h,1)$, `transposeInv3 g` is the transpose inverse ${}^t g^{-1}$, `dualWhittakerFn3 W` is $g\mapsto W(w_{\mathrm{long}}\,{}^tg^{-1})$ with $w_{\mathrm{long}}$ the antidiagonal permutation matrix, `weylPrime3` is the permutation matrix interchanging the last two coordinates, and `modulus` is the normalised module of $\mathbb Q_p$.
--
--   **$\mathrm{GL}_3$ data.** A function $W_3^{\mathrm{base}}:\mathrm{GL}_3(\mathbb Q_p)\to\mathbb C$ is given with: `hW₃law`, the Whittaker transformation law $W_3^{\mathrm{base}}(u(x,y,z)g)=\psi_p^{-1}(x+y)\,W_3^{\mathrm{base}}(g)$ for the upper unipotent matrices `upperUnipotent3 x y z` and the inverse of the standard local additive character; `hW₃sm`, smoothness — some open subgroup of $\mathrm{GL}_3(\mathbb Q_p)$ fixes $W_3^{\mathrm{base}}$ under right translation; `hW₃ne`, $W_3^{\mathrm{base}}\neq 0$; a unitary character $\omega_3$ of $\mathbb Q_p^\times$ (`hω₃u`) which by `hω₃` is the central character, $W_3^{\mathrm{base}}(\mathrm{diag}(t,t,t)h)=\omega_3(t)W_3^{\mathrm{base}}(h)$; `hW₃irr`, irreducibility of the cyclic space `gl3CyclicSubspace W₃base` (the span of the right translates of $W_3^{\mathrm{base}}$) in the form that every non-zero member of it generates $W_3^{\mathrm{base}}$ again; and `hW₃adm`, admissibility: for every open subgroup $U_v$ there is a finite set $B$ of functions whose $\mathbb C$-span contains all $U_v$-right-invariant members of the cyclic space.
--
--   **Gauge.** `hWgauge` provides $B,C\in\mathbb R$ and $t\in\mathbb N$ such that, writing $a(h)=\mathrm{detSize}(h)\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $b(h)=\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ — where $\mathrm{detSize}(h)=\lVert\det h\rVert$, $\mathrm{lastRowSup}(h)$ is the maximum of the norms of the three bottom-row entries, and $\mathrm{minorSup}(h)$ is the maximum of the norms of the three $2\times2$ minors taken from rows $1,2$ — one has $W_3^{\mathrm{base}}(h)=0$ whenever it is not the case that both $a(h)\le B$ and $b(h)\le B$, and $\lVert W_3^{\mathrm{base}}(h)\rVert\le C/(a(h)b(h))^t$ when both hold.
--
--   **Twisting character and principal level.** A unitary character $\chi$ of $\mathbb Q_p^\times$ (`hχu`) has exact conductor exponent $k_p$ in the sense of `HasConductorExponentAt`: $\chi$ is trivial on the higher units `higherUnitsAt ℚ p kp` and for each $m<k_p$ it is non-trivial on `higherUnitsAt ℚ p m`. For a natural number $d$, `hπ₀lev` asserts the existence of a non-zero $W'$ in the cyclic space of $W_3^{\mathrm{base}}$ such that $g\mapsto\chi(\det g)^{-1}W'(g)$ is invariant under right translation by those $k$ in `localMaximalCompact3` all of whose entries of $k-1$ have valuation at most $\exp(-d)$.
--
--   **Gamma data on the $\mathrm{GL}_3$ side.** Characters $\theta_0,\theta_1$ of $\mathbb Q_p^\times$ are given with $\theta_1=1$ (`hθ1`) and $\theta_0$ unitary (`hθu`), together with constants $C_0,C_1\in\mathbb C$ and integers $k_0,k_1$. The hypothesis `h31` asserts, for each $i\in\{0,1\}$ and each $g\in\mathrm{GL}_3(\mathbb Q_p)$, the existence of $Q_1,Q_2$ with $Q_2\neq0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that: the $(3,0)$-integral `localZeta30` of $W_3^{\mathrm{base}}$ twisted by $\theta_i$ converges absolutely for $\mathrm{Re}\,s>\sigma_0$ and satisfies there $\zeta_{3,0}(s,g)\,Q_2(q^{-s})=Q_1(q^{-s})q^{ns}$; the dual $(3,1)$-integral for `dualWhittakerFn3 W₃base`, $\theta_i^{-1}$ at `weylPrime3 * transposeInv3 g` converges absolutely for $\mathrm{Re}\,s>\sigma_1$; and for $\sigma_1<\mathrm{Re}(1-s)$, $\zeta^{\vee}_{3,1}(1-s,g)\,Q_2(q^{-s})=Q_1(q^{-s})q^{ns}\cdot\bigl(C_i\,q^{k_i s}\bigr)$. All these integrals are taken against the multiplicative measure obtained from the self-dual additive Haar measure `selfDualHaarAt ℚ p` (and that measure itself in the $(3,1)$ case).
--
--   **$\mathrm{GL}_2$ data.** An ideal $N\neq\bot$ of $\mathcal O_{\mathbb Q}$ is given (the hypothesis $N\neq\bot$ is named `_hN`), and $w_2^{\mathrm{base}}:\mathrm{GL}_2(\mathbb Q_p)\to\mathbb C$ with: `hw₂law`, the $\psi_p$-Whittaker law for the upper unipotent matrices; `hw₂K`, right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding of the finite-adelic level-$N$ subgroup; `hw₂ne`, $w_2^{\mathrm{base}}\neq0$; `hw₂irr`, irreducibility of the span of its right translates in the same sense as above; `hw₂adm`, admissibility of that span; and `hcentral`, central character $\theta_0$: $w_2^{\mathrm{base}}(\mathrm{diag}(z,z)g)=\theta_0(z)w_2^{\mathrm{base}}(g)$. No assumption is made on the type of this representation. A natural number $b$ satisfies $\mathfrak p^b\mid N$ and $\mathfrak p^{b+1}\nmid N$ (`hNb`), $\theta_0$ is trivial on `higherUnitsAt ℚ p b` (`hcθ`), and the depth conditions are $6(b+3d+3)+7\le k_p$ (`hkC`) and, for a natural number $\Delta$, $6d+18+\Delta\le k_p$ (`hΔ`).
--
--   **Bump vectors for all shallow global twists.** `hbumpAll` asserts: for every character $\xi_A$ of the idele units of $\mathbb Q$ which is an admissible twist (an idele class character, continuous and unitary), unramified at every finite place $v\neq p$, with archimedean component at each real place given by `IsArchCompAt` with parameters $0,0$, and for every $B\in\mathbb N$ with $2d+6\le B$ such that the local component of $\xi_A$ at $p$ has exact conductor exponent $B$, there is a $W_0$ in the cyclic space of $g\mapsto\xi_{A,p}(\det g)\chi(\det g)^{-1}W_3^{\mathrm{base}}(g)$ which is right invariant under `congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ)` (the elements $k$ of the maximal compact whose bottom-row entries $k_{20},k_{21}$ and $k_{22}-1$ all have valuation at most $\exp(-(3B+\Delta))$), satisfies $W_0(\iota(hk))=W_0(\iota(h))$ for $k$ in `localLevelOne … ⊤`, vanishes at $\iota(h)$ unless $h=u(x)k$ for some $x\in\mathbb Q_p$ and some $k$ in `localLevelOne … ⊤`, and is normalised by $W_0(\iota(1))=1$.
--
--   **Uniform $(3,1)$ data, uniformiser, growth and torus finiteness.** `h31all` asserts the existence of $C_{\mathrm{st}}\in\mathbb C$, $y_{\mathrm{st}}\in\mathbb Q_p^\times$, $e_{\mathrm{st}}\in\mathbb N$ and $k_{\mathrm{st}}\in\mathbb Z$ such that for every unitary character $\eta$ of $\mathbb Q_p^\times$ of exact conductor exponent $c_\eta\le b$ and every $g$, the same package of $(3,0)$ and $(3,1)$ convergence and cleared identities as in `h31` holds, with gamma factor $\bigl(C_{\mathrm{st}}\,\eta(y_{\mathrm{st}})^{e_{\mathrm{st}}}\bigr)q^{k_{\mathrm{st}}s}$ independent of $\eta$ apart from the displayed dependence. An element $\varpi$ of the valuation ring has non-zero image (`hπ`) and valuation $\exp(-1)$ (`hϖ`), hence is a uniformiser. `hw₂gr` gives constants $C,A$ with $\lVert w_2^{\mathrm{base}}(\mathrm{diag}(\varpi^m,1)k)\rVert\le C\,q^{Am}$ for all $m\ge0$ and all $k$ in `localLevelOne … ⊤`. `hβ` is the two-variable torus finiteness: for every $g_3\in\mathrm{GL}_3(\mathbb Q_p)$, every $k_0\in\mathrm{GL}_2(\mathbb Q_p)$, every unitary $\eta$ of exact conductor exponent $c\le b$ and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$, there is a finite set $T\subseteq\mathbb Z\times\mathbb Z$ outside of which both of the displayed double integrals vanish — the integral over the units of valuation $1$, against $\eta$, of the $\mu_2$-integral over `localLevelOne … (p.asIdeal ^ b)` of $W_3^{\mathrm{base}}$ evaluated at $\iota\bigl(\varpi^{n_2}\mathbf 1\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k\bigr)g_3$, and its analogue with $\mathrm{dualWhittakerFn3}\bigl(x\mapsto W_3^{\mathrm{base}}(xg_3)\bigr)$ and $k$ replaced by ${}^tk^{-1}$. Finally $w_{0,p}\in\mathrm{GL}_2(\mathbb Q_p)$ has matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`).
--
--   **The abstract functional equation input.** `hΓ` asserts the existence of polynomials $R_1,R_2$ with $R_2\neq0$ and an integer $r$ such that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$ (with its Borel structure) and every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, every $w_2$ in the span of the right translates of $w_2^{\mathrm{base}}$, every $W_3$ in the cyclic space of $W_3^{\mathrm{base}}$, and all $P,P^\vee,Q,Q^\vee$ with $Q\neq0\neq Q^\vee$, integers $m,m^\vee$ and reals $\sigma_2,\sigma_3$: if the two integrability statements and the two cleared identities $\Psi(s)\,Q(q^{-s})=q^{ms}P(q^{-s})$ and $\Psi^\vee(s)\,Q^\vee(q^{-s})=q^{m^\vee s}P^\vee(q^{-s})$ hold on the respective half-planes for the Rankin–Selberg local integrals [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) of $(W_3\circ\iota,w_2)$ and of $\bigl(\mathrm{dualWhittakerFn3}\,W_3\circ\iota,\;g\mapsto|\det g|\,w_2(w_{0,p}\,{}^tg^{-1})\bigr)$, then for all $s$
--   $$R_2(q^{s})\,\bigl(q^{m^\vee s}P^\vee(q^{-s})\bigr)Q(q^{s})=\bigl(R_1(q^{s})q^{rs}\bigr)\bigl(q^{-ms}P(q^{s})\bigr)Q^\vee(q^{-s}).$$
--
--   **Conclusion.** For every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$ and every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, for every $w_2$ in the span of the right translates of $w_2^{\mathrm{base}}$ and every $W_3$ in the cyclic space of $W_3^{\mathrm{base}}$, there exist polynomials $P,P^\vee\in\mathbb C[X]$, integers $m,m^\vee$ and reals $\sigma_2,\sigma_3$ such that the following five assertions hold, all integrals being taken against $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup:
--
--   (i) for $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto W_3(\iota(g))\,w_2(g)\,|\det g|^{s-1/2}$ is integrable;
--
--   (ii) for $\mathrm{Re}\,s>\sigma_3$ the function $g\mapsto \mathrm{dualWhittakerFn3}\,W_3(\iota(g))\cdot|\det g|\,w_2(w_{0,p}\,{}^tg^{-1})\cdot|\det g|^{s-1/2}$ is integrable;
--
--   (iii) for $\mathrm{Re}\,s>\sigma_2$ the Rankin–Selberg local integral of $(W_3\circ\iota, w_2)$ with $\delta(g)=|\det g|$ equals $q^{ms}P(q^{-s})$;
--
--   (iv) for $\mathrm{Re}\,s>\sigma_3$ the Rankin–Selberg local integral of $\bigl(\mathrm{dualWhittakerFn3}\,W_3\circ\iota,\;g\mapsto|\det g|\,w_2(w_{0,p}\,{}^tg^{-1})\bigr)$ equals $q^{m^\vee s}P^\vee(q^{-s})$;
--
--   (v) for all $s\in\mathbb C$,
--   $$q^{m^\vee s}P^\vee(q^{-s})=\bigl(C_0\,q^{-k_0 s}\bigr)\bigl(C_1\,q^{-k_1 s}\bigr)\cdot\bigl(q^{-ms}P(q^{s})\bigr),$$
--   that is, the $\mathrm{GL}_3\times\mathrm{GL}_2$ local gamma factor is the product of the two monomial gamma factors supplied by `h31` for $\theta_0$ and $\theta_1=1$.
--
--   This is the local pair-stability statement in the style of Jacquet–Shalika: for a sufficiently deeply ramified twist on the $\mathrm{GL}_3$ side, the gamma factor of the $\mathrm{GL}_3\times\mathrm{GL}_2$ local integral splits as the product of the gamma factors of the two $\mathrm{GL}_3$ twists by the central character of the $\mathrm{GL}_2$ datum and by the trivial character, with no assumption on the type of the $\mathrm{GL}_2$ representation. It is used to identify the local gamma factor at $p$ with a product of standard root numbers, the form of local input required by the converse-theorem step of the cubic-induction (Langlands–Tunnell) strand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global.lean

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_HeckeTate
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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hω₃u : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω₃ x : ℂˣ) : ℂ)‖ = 1)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (d : ℕ)
    (hπ₀lev : ∃ W' ∈ gl3CyclicSubspace W₃base, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)

    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hθ1 : θ 1 = 1)
    (hθu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((θ 0 z : ℂˣ) : ℂ)‖ = 1)
    (C : Fin 2 → ℂ) (k : Fin 2 → ℤ)
    (h31 : ∀ i : Fin 2,
      ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base (θ i) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (θ i) s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) (θ i)⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base (θ i) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
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

    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ 0 z : ℂˣ) : ℂ) * w₂base g)

    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)

    (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ 0 u = 1)
    (hkC : 6 * (b + 3 * d + 3) + 7 ≤ kp)

    (Δ : ℕ) (hΔ : 6 * d + 18 + Δ ≤ kp)

    (hbumpAll : ∀ (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → NumberField.TateGlobal.IsUnramifiedCharAt ξA v) →
      (∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0) →
      ∀ B : ℕ, 2 * d + 6 ≤ B → LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B →
      ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
          ((NumberField.TateGlobal.localChar ξA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W₃base g),
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ), ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
        (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
          ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
        W₀ (iotaGL 1) = 1)

    (h31all : ∃ (Cst : ℂ) (yst : (p.adicCompletion ℚ)ˣ) (est : ℕ) (kst : ℤ),
      ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
      (∀ z : (p.adicCompletion ℚ)ˣ, ‖((η z : ℂˣ) : ℂ)‖ = 1) →
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
              ((Cst * ((η yst : ℂˣ) : ℂ) ^ est) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((kst : ℂ) * s))))
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
              ((C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
                (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by sorry
