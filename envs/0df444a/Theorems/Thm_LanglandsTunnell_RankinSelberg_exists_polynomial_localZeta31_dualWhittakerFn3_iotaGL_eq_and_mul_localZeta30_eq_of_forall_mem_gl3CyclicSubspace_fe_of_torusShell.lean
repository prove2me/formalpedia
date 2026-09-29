-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
-- name    : LanglandsTunnell.RankinSelberg.exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/77158f7c-abe6-5b3b-855b-1972a03e48c1
-- title:
--   Dual local GL₃timesGL₁ functional equation in Laurent form
-- statement:
--   Let $p$ be a height-one prime of $\mathbb{Z}$, write $F=\mathbb{Q}_p$ for the completion and $q=N(p)$ for the absolute norm of $p$, and let $\varpi$ be an element of the valuation ring whose image in $F$ is non-zero of valuation $\exp(-1)$. Let $\psi$ be an additive character of $F$ which is trivial on $\{|x|\le\exp n\}$ and non-trivial at some $x$ with $|x|\le\exp(n+1)$. Let $V:\mathrm{GL}_3(F)\to\mathbb{C}$ satisfy $V(u(x,y,z)g)=\psi^{-1}(x+y)V(g)$ for the upper unipotent matrices $u(x,y,z)$, and be invariant under right translation by some open subgroup. Let $\chi,\eta:F^\times\to\mathbb{C}^\times$ be characters with $\eta(a)=\chi(a)^{-1}\,\mathrm{modulus}(a)$, let $C\in\mathbb{C}$, $k\in\mathbb{Z}$ and $h\in\mathrm{GL}_2(F)$, and put $\tilde V(g)=V(w_3\,{}^t g^{-1})$ (`dualWhittakerFn3`), $\iota(h)=\mathrm{diag}(h,1)$ and $g'=w'\,{}^t\iota(h)^{-1}$ with $w'$ the transposition matrix `weylPrime3`. Then for every Haar measure $\tau$ on $F^\times$ and additive Haar measure $\nu$ on $F$ the following implication holds. Assume first that for every $h'\in\mathrm{GL}_2(F)$ there is a finite set $T\subset\mathbb{Z}$ with $\int_{|u|=1}\tilde V(\iota(\mathrm{diag}(\varpi^j u,1)h'))\chi(u)^{-1}\,d\tau(u)=0$ for all $j\notin T$; assume second that every $V'$ in the $\mathbb{C}$-span of the right translates of $V$ admits polynomials $Q_1,Q_2$ with $Q_2\ne0$, an integer $n_0$ and reals $\sigma_0,\sigma_1$ such that the $Z_0$-integrand for $(V',\chi,g')$ is integrable for $\mathrm{Re}\,s>\sigma_0$ and there $\mathrm{localZeta30}(V',\chi,s,g')\,Q_2(q^{-s})=Q_1(q^{-s})q^{n_0 s}$, while the $Z_1$-integrand for $(\tilde V',\chi^{-1},w'\,{}^t g'^{-1})$ is integrable for $\mathrm{Re}\,s>\sigma_1$ and $\mathrm{localZetaDual31}(V',\chi,1-s,g')\,Q_2(q^{-s})=Q_1(q^{-s})q^{n_0 s}\,(C\,q^{ks})$ whenever $\mathrm{Re}(1-s)>\sigma_1$. The conclusion is that there exist a polynomial $P$, an integer $m$, reals $\sigma_0,\sigma_1$ and a finite set $R\subset\mathbb{R}$ such that the $Z_1$-integrand for $(\tilde V,\eta,\iota(h))$ is integrable for $\mathrm{Re}\,S>\sigma_0$ with $\mathrm{localZeta31}(\tilde V,\eta,S,\iota(h))=q^{mS}P(q^{-S})$ there, and the $Z_0$-integrand for $(V,\chi,g')$ is integrable for $\mathrm{Re}\,s>\sigma_1$ with $C\,\mathrm{localZeta30}(V,\chi,-S,g')=q^{kS}\,\bigl(q^{mS}P(q^{-S})\bigr)$ for all $S$ with $\mathrm{Re}(-S)>\sigma_1$ and $q^{\mathrm{Re}\,S}\notin R$. Here the convergence predicates assert exactly integrability of the displayed integrands, for $\tau$ on $F^\times$ and for $\tau\otimes\nu$ on $F^\times\times F$ respectively, in the indicated half-planes.
--
--   This is the local $\mathrm{GL}_3\times\mathrm{GL}_1$ functional equation of Jacquet, Piatetski-Shapiro and Shalika, organised for the dual reading: the zeta integral $Z_1$ of the dual Whittaker function at points $\iota(h)$ is exhibited as a Laurent polynomial in $q^{-S}$, and is matched, away from finitely many values of $q^{\mathrm{Re}\,S}$, with $C$ times the $Z_0$-integral of $V$ at $w'\,{}^t\iota(h)^{-1}$. It feeds the computation of the fibres of the unfolded dual $\mathrm{GL}_3\times\mathrm{GL}_2$ integral over the torus and unipotent variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (n : ℤ)
    (hψn : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (V : LocalGL3 p → ℂ) (hV : IsGL3PsiWhittakerFn ψ⁻¹ V)
    (hVsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, V (g * k) = V g)
    (χ η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((η a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ))
    (C : ℂ) (k : ℤ) (h : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],

      (∀ h' : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ j : ℤ, j ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          dualWhittakerFn3 V (iotaGL (diagUnitGL2
            (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ j * u) * h')) *
            ((χ u : ℂˣ) : ℂ)⁻¹ ∂τ = 0) →

      (∀ V' ∈ gl3CyclicSubspace V, ∃ (Q₁ Q₂ : Polynomial ℂ) (n₀ : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p τ V' χ (weylPrime3 * transposeInv3 (iotaGL h)) σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p τ V' χ s (weylPrime3 * transposeInv3 (iotaGL h)) *
                Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p τ ν (dualWhittakerFn3 V') χ⁻¹
            (weylPrime3 * transposeInv3 (weylPrime3 * transposeInv3 (iotaGL h))) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p τ ν V' χ (1 - s) (weylPrime3 * transposeInv3 (iotaGL h)) *
                Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s) *
                (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) →
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ σ₁ : ℝ) (R : Finset ℝ),
        IsLocalZeta31ConvergentAbove p τ ν (dualWhittakerFn3 V) η (iotaGL h) σ₀ ∧
        (∀ S : ℂ, σ₀ < S.re →
          localZeta31 p τ ν (dualWhittakerFn3 V) η S (iotaGL h) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * S) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S))) ∧
        IsLocalZeta30ConvergentAbove p τ V χ (weylPrime3 * transposeInv3 (iotaGL h)) σ₁ ∧
        (∀ S : ℂ, σ₁ < (-S).re → (Ideal.absNorm p.asIdeal : ℝ) ^ S.re ∉ R →
          C * localZeta30 p τ V χ (-S) (weylPrime3 * transposeInv3 (iotaGL h)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * S) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * S) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S)))) := by sorry
