-- Prove2me | Theorems.Thm_ModularForm_exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv
-- name    : ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/bf13f7ac-f7a5-583e-9ea5-70a472500a7d
-- title:
--   Serre's valuation lemma for the level-lowering trace
-- statement:
--   Fix a natural number $M \neq 0$ and a prime $p$, and an Atkin–Lehner datum $W$ at level $M$ for $p$: a natural number $W.R$ with $M = p \cdot W.R$ together with integers $a, b$ satisfying $pa - W.R\,b = 1$, whence an element $W.\mathtt{alGL}$ of $GL_2(\mathbb{R})$ obtained from the associated integral matrix. Let $H \le (\mathbb{Z}/M)^\times$ contain every unit reducing to $1$ in $(\mathbb{Z}/W.R)^\times$, write $H'$ for the image of $H$ in $(\mathbb{Z}/W.R)^\times$, and assume that $\Gamma_H(M) = \{\gamma \in \Gamma_0(M) : \gamma \bmod M \in H\}$, viewed inside $GL_2(\mathbb{R})$, has finite relative index in $\Gamma_{H'}(W.R)$. Let $R_0$ be a commutative ring, $\varphi : R_0 \to \mathbb{C}$ a ring homomorphism, and $I \subseteq R_0$ an ideal containing the image of $p$. Let $g, g_W$ be modular forms of weight $k_1$ and $\varepsilon, \varepsilon_W$ of weight $k_2$ on $\Gamma_H(M)$, with $g_W = g \mid_{k_1} W.\mathtt{alGL}^{-1}$ and $\varepsilon_W = \varepsilon \mid_{k_2} W.\mathtt{alGL}^{-1}$ as functions on the upper half-plane. Let $u, v, s, t \in R_0$, let $c, e, i$ be natural numbers, and let $P_g, P_{g_W}, P_\varepsilon, P_{\varepsilon_W}$ be power series over $R_0$ whose images under $\varphi$, applied coefficientwise, satisfy: $\varphi(P_g) = \varphi(u) \cdot q_\infty(g)$, $\varphi(P_{g_W}) = \varphi(v) p^c \cdot q_\infty(g_W)$, $\varphi(P_\varepsilon) = \varphi(s) \cdot q_\infty(\varepsilon)$ and $p^e \cdot \varphi(P_{\varepsilon_W}) = \varphi(s) \cdot q_\infty(\varepsilon_W)$, where $q_\infty$ denotes the $q$-expansion of width $1$ at $\infty$; assume further that $P_\varepsilon$ reduces modulo $I$ to the constant series $t \bmod I$, and that $i + c < e\,i$. The conclusion asserts the existence of a power series $P$ over $R_0$ with $\varphi(P)$ equal to the $q$-expansion of width $1$ of the function $\varphi(u v s^i) \cdot \mathrm{Tr}(g \varepsilon^i)$, where $\mathrm{Tr}$ is the trace from $\Gamma_H(M)$ to $\Gamma_{H'}(W.R)$, and with $P \equiv (v t^i) \cdot P_g \pmod I$ coefficientwise.
--
--   This is Serre's valuation lemma as used in level lowering at a prime dividing the level exactly once: the trace from $\Gamma_H(M)$ to $\Gamma_{H'}(M/p)$ of $g\varepsilon^i$ has a $q$-expansion that, after the indicated rescaling, lies in $R_0$ and is congruent modulo $I$ to a multiple of that of $g$, the auxiliary form $\varepsilon$ replacing Serre's Eisenstein series and $R_0$ being an arbitrary coefficient ring. It is stated so as to exhibit the trace itself, allowing its behaviour at other cusps to be examined afterwards, and is used in the construction of forms with prescribed integrality and congruence properties at two cusps ([`CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet`](thm.html#CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ))]
    {R₀ : Type*} [CommRing R₀] (φ : R₀ →+* ℂ) (I : Ideal R₀) (hpI : ((p : ℕ) : R₀) ∈ I)
    {k₁ k₂ : ℤ} (g gW : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k₁)
    (ε εW : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hgW : (⇑gW : UpperHalfPlane → ℂ) = (⇑g : UpperHalfPlane → ℂ) ∣[k₁] W.alGL⁻¹)
    (hεW : (⇑εW : UpperHalfPlane → ℂ) = (⇑ε : UpperHalfPlane → ℂ) ∣[k₂] W.alGL⁻¹)
    (u v s t : R₀) (c e : ℕ) (Pg PgW Pε PεW : PowerSeries R₀)
    (hg : Pg.map φ = φ u • UpperHalfPlane.qExpansion 1 (⇑g : UpperHalfPlane → ℂ))
    (hgW' : PgW.map φ = (φ v * (p : ℂ) ^ c) • UpperHalfPlane.qExpansion 1 (⇑gW : UpperHalfPlane → ℂ))
    (hε : Pε.map φ = φ s • UpperHalfPlane.qExpansion 1 (⇑ε : UpperHalfPlane → ℂ))
    (hεI : Pε.map (Ideal.Quotient.mk I) = PowerSeries.C (Ideal.Quotient.mk I t))
    (hεW' : ((p : ℂ) ^ e) • PεW.map φ = φ s • UpperHalfPlane.qExpansion 1 (⇑εW : UpperHalfPlane → ℂ))
    (i : ℕ) (hi : i + c < e * i) :
    ∃ P : PowerSeries R₀,
      P.map φ = UpperHalfPlane.qExpansion 1
        (φ (u * v * s ^ i) • (⇑(ModularForm.trace
          (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ))
          (g.mul (ε.pow i))) : UpperHalfPlane → ℂ)) ∧
      P.map (Ideal.Quotient.mk I) = (PowerSeries.C (v * t ^ i) * Pg).map (Ideal.Quotient.mk I) := by sorry
