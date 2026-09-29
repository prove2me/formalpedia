-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
-- name    : LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/8689ef04-31b1-5a49-8296-9b3b3c0a10f6
-- title:
--   Polynomial decay of a dual archimedean zeta integral on strips
-- statement:
--   Fix a real archimedean parameter $P_2$ and an archimedean $\mathrm{GL}(2)$ datum $D$ for $P_2$ (a Whittaker-type function $W$ on $2\times 2$ real matrices with the smoothness, unipotent and central transformation laws, zeta integrals satisfying the stated integrability, Gamma-factor identity, functional equation, finite-order and decay properties), a complex exponent $u_3$ and a sign $a_3\in\mathbb{Z}/2$. Let $E$ be a monoid homomorphism from the units of the infinite adele ring of $\mathbb{Q}$ to the units of the full adele ring splitting the archimedean units, in the sense that for every $u$ the infinite component of $E u$ is $u$ and its finite component is $1$. Let $a\in\mathbb{Q}$ be nonzero and let $\psi_\infty$ be the additive character $x\mapsto \psi_{\mathrm{arch}}(a x)$ of the infinite adele ring, with $\psi_{\mathrm{arch}}$ the standard archimedean character. Let $\nu_{\mathrm{add}}$ be the measure $|a|^{1/2}$ times the transport of Lebesgue measure on the mixed space along the inverse of the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace`, and let $\nu_{\mathrm{mul}}$ be a Haar measure on the units of the infinite adele ring. Let $S$ lie in `polyGauss3`, that is $S(M)=p(M)\exp(-\pi\sum_{i,b}M_{ib}^2)$ for a complex polynomial $p$ in the entries of a $2\times 3$ real matrix. Let $c_1$ be a real number such that for each $a\in\mathbb{Z}/2$ every $\mu$ in the real Gamma-parameter multiset of $P_2^{\vee}$ twisted by $(0,a)$ satisfies $-\operatorname{Re}\mu<c_1$, and likewise every $\nu$ in its complex Gamma-parameter multiset. Let $\sigma$ be an admissible twist of $\mathbb{Q}$, i.e. a continuous unitary homomorphism from the idele units to $\mathbb{C}^\times$ trivial on principal ideles, and suppose that at every real infinite place $v$ its archimedean local component is $x\mapsto \|x\|^{\mathrm{mult}(v)\,t}\,(x/\|x\|)^{e}$ for some $t\in\mathbb{C}$ and $e\in\mathbb{Z}$. Finally fix $g_\infty\in \mathrm{GL}_3$ of the infinite adele ring, reals $\sigma_1,\sigma_2$, a natural number $N$, and assume $\max(c_1,\operatorname{Re}u_3)+\operatorname{Re}t<\sigma_1$. Then there are real constants $C$ and $T_0$ such that for every $s$ with $\sigma_1\le \operatorname{Re}s\le\sigma_2$ and $|\operatorname{Im}s|\ge T_0$ one has $|\operatorname{Im}s|^N\,\|Z\| \le C$, where $Z$ is the value at $s$ and at the identity of `archZetaDual31` for the measures $\nu_{\mathrm{mul}},\nu_{\mathrm{add}}$, the character $\sigma\circ E$ of the archimedean units, and the vector $h\mapsto$ `jacquetVector3` $D\,u_3\,a_3\,a\,\psi_\infty\,S\,(h g_\infty)$; unfolding the definitions, $Z$ is the $\mathrm{GL}(3)$ mirabolic double integral of the dual Whittaker function $g\mapsto \mathrm{jacquetVector3}(\cdots)(w_3\,{}^t g^{-1} g_\infty)$ against $\sigma^{-1}\circ E$ and $\|\cdot\|^{s-1}$, evaluated at `weylPrime3`.
--
--   This is the archimedean analytic input to the converse theorem in the cubic induction step of the Langlands–Tunnell argument: the explicit polynomial-times-Gaussian Jacquet vector on $\mathrm{GL}_3$ over the infinite adeles of $\mathbb{Q}$ has dual zeta integral decaying faster than any power of the height in closed vertical strips to the right of the abscissa $\max(c_1,\operatorname{Re}u_3)+\operatorname{Re}t$. It is used by [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package), which collects the archimedean properties required to apply the converse theorem for $\mathrm{GL}(3)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
    (P₂ : RealArchParam) (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁))
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ)
    (t : ℂ) (e : ℤ) (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₁ σ₂ : ℝ) (N : ℕ)
    (hσ₁ : max c₁ u₃.re + t.re < σ₁) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      |s.im| ^ N *
        ‖archZetaDual31 ν_mul ν_add (fun h => (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (h * gInf)) (σ.comp E) s 1‖ ≤
          C := by sorry
