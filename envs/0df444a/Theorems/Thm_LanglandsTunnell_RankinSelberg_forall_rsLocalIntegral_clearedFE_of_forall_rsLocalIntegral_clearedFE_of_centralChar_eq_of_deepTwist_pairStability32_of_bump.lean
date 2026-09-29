-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_of_forall_rsLocalIntegral_clearedFE_of_centralChar_eq_of_deepTwist_pairStability32_of_bump
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_of_forall_rsLocalIntegral_clearedFE_of_centralChar_eq_of_deepTwist_pairStability32_of_bump
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/65bcf38f-a8c8-571f-82fc-a41a6e916c1d
-- title:
--   Pair stability at (3,2): transfer of the cleared functional equation
-- statement:
--   Throughout, $p$ is a nonzero prime of $\mathcal O_{\mathbb Q}$, $K_p$ denotes the completion `p.adicCompletion ℚ`, $q :=$ `Ideal.absNorm p.asIdeal`, and $\psi_p$ denotes the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65).
--
--   *Characters.* Four continuous characters $\omega_3,\chi,\xi,\theta_0 : K_p^\times \to \mathbb C^\times$ are given, each assumed unitary in the pointwise sense ($\lVert\omega_3(x)\rVert = 1$ for all $x$, and likewise `hχu`, `hξu`, `hθu`). The natural numbers $k_p$ and $B$ are exact conductor exponents for $\chi$ and for $\xi$ in the sense of `HasConductorExponentAt`: the character is trivial on `higherUnitsAt ℚ p` at that level (the units $u$ with $v(u)=1$ and either level $0$ or $v(u-1)\le q^{-\text{level}}$) and, for every smaller $m$, non-trivial on some unit of `higherUnitsAt ℚ p m`. A further natural number $f$ is given. For $\theta_0$ only the one-sided condition `hcθ` is imposed: $\theta_0$ is trivial on `higherUnitsAt ℚ p b` for a given $b\in\mathbb N$.
--
--   *The two $GL_3$ models.* For $i = 1,2$, a function $W_i$ on $GL_3(K_p)$ is given together with: `hWilaw`, the Whittaker law $W_i(u(x,y,z)\,g) = \psi_p^{-1}(x+y)\,W_i(g)$ for the upper unipotent matrix $u(x,y,z) = \begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$; `hWism`, smoothness, i.e. the existence of an open subgroup $U_v \le GL_3(K_p)$ under which $W_i$ is right invariant; and `hωi`, the central character law $W_i(t\cdot 1_3\, h) = \omega_3(t)\,W_i(h)$, the same $\omega_3$ for both. A natural number $d_i$ is given together with the deep-twist level hypothesis `hlevi`: some $W' \neq 0$ in `gl3CyclicSubspace W1` (respectively `gl3CyclicSubspace W2`), the $\mathbb C$-span of the right translates of $W_i$, satisfies $\chi(\det(gk))^{-1}W'(gk) = \chi(\det g)^{-1}W'(g)$ for all $g$ and all $k$ in `localMaximalCompact3 (𝓞 ℚ) ℚ p` (matrices $k$ with all entries of $k$ and of $k^{-1}$ of valuation $\le 1$) whose entries satisfy $v(k_{ij} - \delta_{ij}) \le q^{-d_i}$; that is, the $\chi^{-1}\!\circ\!\det$-twist of $W'$ is right invariant under the principal congruence subgroup of level $d_i$.
--
--   *The $GL_2$ partner.* An ideal $N$ of $\mathcal O_{\mathbb Q}$ is given with $N \neq \bot$ (`hN`) and $p^b \mid N$, $p^{b+1} \nmid N$ (`hNb`). A function $w_{2,\mathrm{base}}$ on $GL_2(K_p)$ is given, subject to: `hw₂law`, $w_{2,\mathrm{base}}(n(x)g) = \psi_p(x)\,w_{2,\mathrm{base}}(g)$ for the unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hw₂K`, right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $GL_2(K_p)\to GL_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the finite-adelic level-$N$ subgroup; `hw₂ne`, $w_{2,\mathrm{base}} \neq 0$; `hw₂irr`, irreducibility of the cyclic module, namely that every non-zero element $w$ of the span of the right translates of $w_{2,\mathrm{base}}$ has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$; `hw₂adm`, admissibility, namely that for every open subgroup $U \le GL_2(K_p)$ there is a finite set of functions whose span contains every right-$U$-invariant element of the span of the right translates of $w_{2,\mathrm{base}}$; and `hcentral`, the central character law $w_{2,\mathrm{base}}(z\cdot 1_2\,g) = \theta_0(z)\,w_{2,\mathrm{base}}(g)$. Finally $w_{0p} \in GL_2(K_p)$ has underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   *Numerical thresholds.* The five inequalities $2\max(d_1,d_2) + 2 \le B$, $B < k_p$, $f \le k_p$, $f + 2\max(d_1,d_2) + 3 \le 2k_p$ and $2b + 1 \le k_p$ are assumed.
--
--   *Bump hypotheses.* For $i = 1,2$, `hbumpi` asserts the existence of $W_0$ in the span of the right translates of $g \mapsto \xi(\det g)\chi(\det g)^{-1}W_i(g)$ with four properties: $W_0$ is right invariant under the set `congruenceK1 (𝓞 ℚ) ℚ p f` (those $k$ in `localMaximalCompact3` with $v(k_{20}), v(k_{21}), v(k_{22}-1) \le q^{-f}$); the restriction of $W_0$ along the embedding `iotaGL` $h \mapsto \mathrm{diag}(h,1)$ is right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178); this restriction vanishes off the product of the unipotent subgroup $\{n(x)\}$ with that level-one subgroup, i.e. $W_0(\iota(h)) \neq 0$ forces $h = n(x)k$ for some $x \in K_p$ and some $k$ in `localLevelOne ... ⊤`; and $W_0(\iota(1)) = 1$.
--
--   *Rationality hypotheses.* For $i = 1,2$, `hrati` asserts, with $GL_2(K_p)$ carrying the Borel $\sigma$-algebra `localGLBorel ℚ p`: for every Haar measure $\mu_2$ on $GL_2(K_p)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom` (the subgroup $\{n(x)\}$), every $w_2$ in the span of the right translates of $w_{2,\mathrm{base}}$ and every $W_3$ in `gl3CyclicSubspace Wi`, there exist polynomials $P, P^{\vee}, Q, Q^{\vee} \in \mathbb C[X]$, integers $m, m^{\vee}$ and reals $\sigma_2, \sigma_3$ with $Q \neq 0$, $Q^{\vee} \neq 0$ such that four clauses hold, all integrals being taken against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$: for $\operatorname{Re} s > \sigma_2$ the function $g \mapsto W_3(\iota(g))\,w_2(g)\,|\!\det g|^{\,s-1/2}$ is integrable, where $|\cdot|$ is `modulus`; for $\operatorname{Re} s > \sigma_3$ the dual function $g \mapsto W_3^{\vee}(\iota(g))\,|\!\det g|\,w_2(w_{0p}\,{}^t\!g^{-1})\,|\!\det g|^{\,s-1/2}$ is integrable, where $W_3^{\vee} =$ `dualWhittakerFn3 W₃`, $W_3^{\vee}(g) = W_3(w_3\,{}^t\!g^{-1})$ with $w_3$ the $3\times 3$ antidiagonal permutation matrix; for $\operatorname{Re} s > \sigma_2$, the Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) of the pair $(g \mapsto W_3(\iota(g)),\,w_2)$ with $\delta = |\!\det\cdot|$ satisfies $\Psi(s)\,Q(q^{-s}) = q^{ms}P(q^{-s})$; and for $\operatorname{Re} s > \sigma_3$ the corresponding dual integral satisfies $\Psi^{\vee}(s)\,Q^{\vee}(q^{-s}) = q^{m^{\vee}s}P^{\vee}(q^{-s})$.
--
--   *Functional-equation hypotheses.* `hΓ₁` asserts the existence of $R_1, R_2 \in \mathbb C[X]$ and $r \in \mathbb Z$ with $R_2 \neq 0$ such that for all Haar measures $\mu_2, \mu_{N_2}$ as above, all $w_2$ in the span of the right translates of $w_{2,\mathrm{base}}$, all $W_3 \in$ `gl3CyclicSubspace W1`, and all $P, P^{\vee}, Q, Q^{\vee}, m, m^{\vee}, \sigma_2, \sigma_3$ with $Q \neq 0$, $Q^{\vee} \neq 0$ for which the two integrability clauses and the two rationality identities just described hold, one has the cleared functional equation
--   $$R_2(q^{s})\,\bigl(q^{m^{\vee}s}P^{\vee}(q^{-s})\bigr)\,Q(q^{s}) = \bigl(R_1(q^{s})\,q^{rs}\bigr)\,\bigl(q^{-ms}P(q^{s})\bigr)\,Q^{\vee}(q^{-s}) \qquad \text{for all } s \in \mathbb C.$$
--   Separately, polynomials $R_1, R_2 \in \mathbb C[X]$ and an integer $r$ are given with $R_2 \neq 0$ (`hR₂`), together with `hFE₂`: the same cleared functional equation, with these $R_1, R_2, r$, holds for all $\mu_2$, $\mu_{N_2}$, all $w_2$ in the span of the right translates of $w_{2,\mathrm{base}}$, all $W_3 \in$ `gl3CyclicSubspace W2`, and all $P, P^{\vee}, Q, Q^{\vee}, m, m^{\vee}, \sigma_2, \sigma_3$ with $Q \neq 0$, $Q^{\vee} \neq 0$ satisfying the two integrability clauses and the two rationality identities for $W_3$.
--
--   *Conclusion.* The same triple $(R_1, R_2, r)$ serves the first model: for every Haar measure $\mu_2$ on $GL_2(K_p)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, every $w_2$ in the span of the right translates of $w_{2,\mathrm{base}}$, every $W_3 \in$ `gl3CyclicSubspace W1`, and all $P, P^{\vee}, Q, Q^{\vee} \in \mathbb C[X]$, $m, m^{\vee} \in \mathbb Z$, $\sigma_2, \sigma_3 \in \mathbb R$ with $Q \neq 0$ and $Q^{\vee} \neq 0$: if $g \mapsto W_3(\iota(g))\,w_2(g)\,|\!\det g|^{\,s-1/2}$ is integrable for $\operatorname{Re} s > \sigma_2$, if $g \mapsto W_3^{\vee}(\iota(g))\,|\!\det g|\,w_2(w_{0p}\,{}^t\!g^{-1})\,|\!\det g|^{\,s-1/2}$ is integrable for $\operatorname{Re} s > \sigma_3$ (both against $\mu_2$ weighted by the [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$), if $\Psi(s)\,Q(q^{-s}) = q^{ms}P(q^{-s})$ for $\operatorname{Re} s > \sigma_2$, and if $\Psi^{\vee}(s)\,Q^{\vee}(q^{-s}) = q^{m^{\vee}s}P^{\vee}(q^{-s})$ for $\operatorname{Re} s > \sigma_3$, then for every $s \in \mathbb C$
--   $$R_2(q^{s})\,\bigl(q^{m^{\vee}s}P^{\vee}(q^{-s})\bigr)\,Q(q^{s}) = \bigl(R_1(q^{s})\,q^{rs}\bigr)\,\bigl(q^{-ms}P(q^{s})\bigr)\,Q^{\vee}(q^{-s}).$$
--
--   This is the Jacquet–Shalika stability statement for pairs at $(3,2)$ in the form used in the cubic-induction step: two deeply $\chi$-twisted $GL_3$ Whittaker models with the same central character, each admitting the bump vector of level $f$, share one and the same cleared $GL_3 \times GL_2$ functional-equation datum $(R_1,R_2,r)$ against every partner of exact level $b$ at $p$, so the datum may be transported from the second model to the first. It feeds the comparison of local Rankin–Selberg integrals and their duals that underlies the converse-theorem input to the Langlands–Tunnell argument; the algebraic transfer rests on the two cleared-functional-equation manipulations [`LanglandsTunnell.forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero`](thm.html#LanglandsTunnell.forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero) and [`LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq`](thm.html#LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq), together with the datum produced by [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_clearedFE_datum_of_centralChar_eq_of_deepTwist_pairStability32_of_bump`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_clearedFE_datum_of_centralChar_eq_of_deepTwist_pairStability32_of_bump).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_of_forall_rsLocalIntegral_clearedFE_of_centralChar_eq_of_deepTwist_pairStability32_of_bump.lean

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

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_of_forall_rsLocalIntegral_clearedFE_of_centralChar_eq_of_deepTwist_pairStability32_of_bump
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hω₃u : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω₃ x : ℂˣ) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)

    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B) (f : ℕ)

    (W1 : LocalGL3 p → ℂ)
    (hW1law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W1)
    (hW1sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W1 (g * k) = W1 g)
    (hω1 : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W1 (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W1 h)

    (d₁ : ℕ)
    (hlev1 : ∃ W' ∈ gl3CyclicSubspace W1, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d₁ : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)

    (W2 : LocalGL3 p → ℂ)
    (hW2law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W2)
    (hW2sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W2 (g * k) = W2 g)
    (hω2 : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W2 (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W2 h)

    (d₂ : ℕ)
    (hlev2 : ∃ W' ∈ gl3CyclicSubspace W2, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d₂ : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hθu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((θ₀ z : ℂˣ) : ℂ)‖ = 1)
    (b : ℕ) (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ₀ u = 1)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
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
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (hB : 2 * max d₁ d₂ + 2 ≤ B) (hBk : B < kp) (hfk : f ≤ kp) (hfk2 : f + 2 * max d₁ d₂ + 3 ≤ 2 * kp) (hbk : 2 * b + 1 ≤ kp)

    (hbump1 : ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W1 g),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
        ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
      W₀ (iotaGL 1) = 1)

    (hbump2 : ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
        ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
      W₀ (iotaGL 1) = 1)

    (hrat1 :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W1,
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
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))

    (hrat2 :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W2,
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
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))

    (hΓ₁ :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W1,
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
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))

    (R₁ R₂ : Polynomial ℂ) (r : ℤ) (hR₂ : R₂ ≠ 0)
    (hFE₂ :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W2,
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
        ∀ W₃ ∈ gl3CyclicSubspace W1,
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
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
