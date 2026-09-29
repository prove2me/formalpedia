-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_eq_laurent_of_deepTwist_of_principalLevel_of_admissible
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_eq_laurent_of_deepTwist_of_principalLevel_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/7064f066-4939-5cf5-b528-abb9056bd3be
-- title:
--   Deep twist: GL₃timesGL₂ local integrals are Laurent polynomials
-- statement:
--   Throughout, $p$ is a finite place of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$; write $F_p = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, $q =$ `Ideal.absNorm p.asIdeal` for the residue cardinality, $\psi_p$ for the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), and $|\cdot|$ for [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15), the module of $F_p$ (the scaling factor of additive Haar measure). The multiplicative measure used on $F_p^\times$ is `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))`, obtained from the self-dual additive Haar measure by weighting with $|\cdot|^{-1}$ and restricting to the units. `LocalGL3 p` is $\mathrm{GL}_3(F_p)$.
--
--   **The $\mathrm{GL}_3$ vector.** A function $W_3^{\mathrm{base}} \colon \mathrm{GL}_3(F_p) \to \mathbb{C}$ is given, subject to: `hW₃law`, that $W_3^{\mathrm{base}}(u(x,y,z)g) = \psi_p^{-1}(x+y)\,W_3^{\mathrm{base}}(g)$ for all $x,y,z \in F_p$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix `upperUnipotent3 x y z`; `hW₃sm`, that $W_3^{\mathrm{base}}$ is invariant under right translation by some open subgroup of $\mathrm{GL}_3(F_p)$; `hW₃ne`, that $W_3^{\mathrm{base}} \neq 0$; `hω₃`, that $W_3^{\mathrm{base}}(\mathrm{diag}(t,t,t)\,h) = \omega_3(t)W_3^{\mathrm{base}}(h)$ for a homomorphism $\omega_3 \colon F_p^\times \to \mathbb{C}^\times$; `hW₃irr`, that every non-zero element $W$ of `gl3CyclicSubspace W₃base` — the $\mathbb{C}$-span of the right translates $g \mapsto W_3^{\mathrm{base}}(gh)$, $h \in \mathrm{GL}_3(F_p)$ — has $W_3^{\mathrm{base}}$ in its own cyclic span; and `hW₃adm`, that for every open subgroup $U_v \le \mathrm{GL}_3(F_p)$ there is a finite family $B$ of functions $\mathrm{GL}_3(F_p) \to \mathbb{C}$ such that every member of `gl3CyclicSubspace W₃base` invariant under right translation by $U_v$ lies in the span of $B$.
--
--   **The gauge hypothesis `hWgauge`.** There are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, writing $a(h) = \mathrm{detSize}(h)\,\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $b(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ — where `detSize` is $\|\det h\|$, `lastRowSup` the maximum of the norms of the entries of the last row, and `minorSup` the maximum of the norms of the three $2\times 2$ minors formed from the last two rows — one has $W_3^{\mathrm{base}}(h)=0$ whenever not both $a(h)\le B$ and $b(h)\le B$, and $\|W_3^{\mathrm{base}}(h)\| \le C/(a(h)b(h))^t$ whenever both hold.
--
--   **The twisting character and the level of the untwisted model.** A homomorphism $\chi \colon F_p^\times \to \mathbb{C}^\times$ is given with $\|\chi(x)\| = 1$ for all $x$ (`hχu`), together with $k_p \in \mathbb{N}$ such that `HasConductorExponentAt ℚ p χ kp` holds, i.e. $\chi$ is trivial on the set of units $u$ with $|u|=1$ and ($k_p = 0$ or $|u-1| \le q^{-k_p}$), while for each $m < k_p$ some unit in the corresponding level-$m$ set is not killed by $\chi$. A natural number $d$ is given and `hπ₀lev` asserts the existence of a non-zero $W'$ in `gl3CyclicSubspace W₃base` such that $\chi(\det(gk))^{-1}W'(gk) = \chi(\det g)^{-1}W'(g)$ for all $g$ and all $k$ in `localMaximalCompact3 (𝓞 ℚ) ℚ p` (the matrices with all entries of $k$ and of $k^{-1}$ of valuation $\le 1$) whose entries satisfy $v(k_{ij} - \delta_{ij}) \le q^{-d}$; that is, the untwisted function $\chi^{-1}\!\circ\!\det \cdot W'$ is fixed by the principal congruence subgroup of level $d$.
--
--   **The two auxiliary characters and the $(3,0)$–$(3,1)$ functional equations.** Two homomorphisms $\theta_0,\theta_1 \colon F_p^\times \to \mathbb{C}^\times$ are given with $\theta_1 = 1$ (`hθ1`) and $\theta_0$ unitary (`hθu`), together with constants $C_0,C_1 \in \mathbb{C}$ and integers $k_0,k_1$. The hypothesis `h31` requires, for each $i \in \{0,1\}$ and each $g \in \mathrm{GL}_3(F_p)$, polynomials $Q_1,Q_2 \in \mathbb{C}[X]$ with $Q_2 \neq 0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that: the integrand $a \mapsto W_3^{\mathrm{base}}(\iota(\mathrm{diag}(a,1))g)\theta_i(a)|a|^{s-1}$ is integrable for $\mathrm{Re}\,s > \sigma_0$ (`IsLocalZeta30ConvergentAbove`); $\mathrm{Z}_{3,0}(s,g)\,Q_2(q^{-s}) = Q_1(q^{-s})q^{ns}$ for $\mathrm{Re}\,s > \sigma_0$, where $\mathrm{Z}_{3,0}$ is `localZeta30`, the integral of that integrand; the analogous two-variable integrand for `localZeta31` with the dual Whittaker function `dualWhittakerFn3 W₃base` (that is, $h \mapsto W_3^{\mathrm{base}}(w_{\mathrm{long}}\,{}^{t}h^{-1})$), the character $\theta_i^{-1}$ and the argument `weylPrime3 * transposeInv3 g` is integrable for $\mathrm{Re}\,s > \sigma_1$ (`IsLocalZeta31ConvergentAbove`); and, for all $s$ with $\sigma_1 < \mathrm{Re}(1-s)$, the dual zeta integral `localZetaDual31` at $1-s$ satisfies $\mathrm{Z}^{\vee}_{3,1}(1-s,g)\,Q_2(q^{-s}) = Q_1(q^{-s})\,q^{ns}\,\bigl(C_i\,q^{k_i s}\bigr)$, i.e. the functional equation with monomial $\gamma$-factor $C_i q^{k_i s}$.
--
--   **The $\mathrm{GL}_2$ vector and its level.** An ideal $N \neq \bot$ of $\mathcal{O}_{\mathbb{Q}}$ and a function $w_2^{\mathrm{base}} \colon \mathrm{GL}_2(F_p) \to \mathbb{C}$ are given with: `hw₂law`, $w_2^{\mathrm{base}}\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr.g) = \psi_p(x)w_2^{\mathrm{base}}(g)$; `hw₂K`, right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding of the finite-adelic level-$N$ congruence subgroup; `hw₂ne`, $w_2^{\mathrm{base}} \neq 0$; `hw₂irr`, the analogue of `hW₃irr` for the span of the right translates of $w_2^{\mathrm{base}}$; `hw₂adm`, the analogue of `hW₃adm` for that span; and `hcentral`, $w_2^{\mathrm{base}}(\mathrm{diag}(z,z)g) = \theta_0(z)w_2^{\mathrm{base}}(g)$, so that $\theta_0$ is the central character of the $\mathrm{GL}_2$ side. A natural number $b$ is given with `hNb`: $p^b \mid N$ and $p^{b+1} \nmid N$. Further, `hcθ` requires $\theta_0$ to be trivial on `higherUnitsAt ℚ p b`, and `hkC` imposes the depth inequality $6(b + 3d + 3) + 7 \le k_p$.
--
--   **Uniformiser, growth and torus–shell vanishing.** An element $\varpi$ of the valuation ring is given with non-zero image in $F_p$ (`hπ`) and valuation $q^{-1}$ (`hϖ`). The hypothesis `hw₂gr` provides reals $C, A$ with $\|w_2^{\mathrm{base}}(\mathrm{diag}(\varpi^m,1)k)\| \le C\,q^{Am}$ for all $m \ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178). The hypothesis `hβ` requires, for every $g_3 \in \mathrm{GL}_3(F_p)$, every $k_0 \in \mathrm{GL}_2(F_p)$, every homomorphism $\eta \colon F_p^\times \to \mathbb{C}^\times$ with conductor exponent $c \le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(F_p)$, a finite set $T \subseteq \mathbb{Z} \times \mathbb{Z}$ outside which both of the following double integrals vanish: the integral over the unit shell $\{u : |u| = 1\}$, against $\eta(u)$ and the multiplicative measure, of $\int_{k} W_3^{\mathrm{base}}\bigl(\iota\bigl(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,(k_0k)\bigr)g_3\bigr)\,d\mu_2(k)$ over $k$ in the level-$p^b$ subgroup, and the same expression with $W_3^{\mathrm{base}}(\,\cdot\,)$ replaced by `dualWhittakerFn3` applied to $x \mapsto W_3^{\mathrm{base}}(xg_3)$ and with $k$ replaced by ${}^{t}k^{-1}$ ([`AutomorphicForm.transposeInvN`](def/AutomorphicForm_SmoothingKernel.html#L28)). Finally $w_{0,p} \in \mathrm{GL}_2(F_p)$ is the matrix $\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$ (`hw₀p`).
--
--   **Conclusion.** For every Haar measure $\mu_2$ on $\mathrm{GL}_2(F_p)$ (for the Borel structure `localGLBorel`), every Haar measure $\mu_{N_2}$ on the image of `unipotentGL2Hom`, that is on the upper unipotent subgroup $\{\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)\}$, every $w_2$ in the span of the right translates of $w_2^{\mathrm{base}}$ and every $W_3 \in$ `gl3CyclicSubspace W₃base`, there exist polynomials $P, P^{\vee} \in \mathbb{C}[X]$, integers $m, m^{\vee}$ and reals $\sigma_2,\sigma_3$ such that the following four assertions hold, all integrals being taken with respect to $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup for $\mu_{N_2}$:
--
--   1. for every $s$ with $\mathrm{Re}\,s > \sigma_2$, the function $g \mapsto W_3(\iota(g))\,w_2(g)\,|\det g|^{\,s-1/2}$ is integrable;
--
--   2. for every $s$ with $\mathrm{Re}\,s > \sigma_3$, the function $g \mapsto \bigl(\mathrm{dualWhittakerFn3}\,W_3\bigr)(\iota(g))\cdot |\det g|\,w_2\bigl(w_{0,p}\,{}^{t}g^{-1}\bigr)\cdot |\det g|^{\,s-1/2}$ is integrable;
--
--   3. for every $s$ with $\mathrm{Re}\,s > \sigma_2$, the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) for the pair $\bigl(g \mapsto W_3(\iota(g)),\,w_2\bigr)$ with $\delta(g) = |\det g|$ equals $q^{ms}\,P(q^{-s})$;
--
--   4. for every $s$ with $\mathrm{Re}\,s > \sigma_3$, the local Rankin–Selberg integral for the pair $\bigl(g \mapsto (\mathrm{dualWhittakerFn3}\,W_3)(\iota(g)),\, g \mapsto |\det g|\,w_2(w_{0,p}\,{}^{t}g^{-1})\bigr)$ equals $q^{m^{\vee}s}\,P^{\vee}(q^{-s})$.
--
--   Here $\iota$ is the embedding `iotaGL` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ in the upper left block, and `rsLocalIntegral` is by definition $\int (W(g)F(g))\,|\det g|^{\,s-1/2}$ against the same weighted measure, so that conjuncts 1 and 3, respectively 2 and 4, concern the same integral. Thus each of the two local integrals is, on its half-plane of absolute convergence, a Laurent polynomial in $q^{-s}$. No relation between the two integrals is asserted; in particular the constants $C_i$ and exponents $k_i$ of the monomial $\gamma$-factors occur only in the hypothesis `h31`, not in the conclusion.
--
--   This is the local half, over the place $p$ of $\mathbb{Q}$, of the Jacquet–Shalika analysis of $\mathrm{GL}_3 \times \mathrm{GL}_2$ Rankin–Selberg integrals when the $\mathrm{GL}_3$ vector is a deep twist by a highly ramified character: it yields absolute convergence on a half-plane and the Laurent-polynomial shape of both the integral and its dual, for every pair of vectors in the two cyclic spans. It is used by [`LanglandsTunnell.RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep) and by [`LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global`](thm.html#LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global), where it is combined with a test-vector computation and a vector-independent $\gamma$-factor to show that the local $L$-factor of the twisted pair is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_eq_laurent_of_deepTwist_of_principalLevel_of_admissible.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_eq_laurent_of_deepTwist_of_principalLevel_of_admissible
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
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
