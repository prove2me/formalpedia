-- Prove2me | Theorems.Thm_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
-- name    : ModularCurve.exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/89b3ee38-7dcb-561f-94d0-0c812444ba76
-- title:
--   Galois conjugation of Atkin–Lehner expansions over an abstract cyclotomic field
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \nmid M$, let $k$ be an even integer, and let $f$ be a modular form of weight $k$ for $\Gamma_1(Mp)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume $f$ has integral $q$-expansion in the sense of [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37): there is a power series $p_0$ over $\mathbb{Z}$ whose image under the ring homomorphism $\mathbb{Z} \to \mathbb{C}$ is the period-$1$ $q$-expansion of $f$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ with $p \mid \gamma_{11}$ (the lower-right entry). Let $L$ be a field of characteristic zero which is a $p$-th cyclotomic extension of $\mathbb{Q}$, let $\zeta \in L$ be a primitive $p$-th root of unity, let $\iota\colon L \to \mathbb{C}$ be a ring homomorphism, let $s$ be a $\mathbb{Q}$-algebra automorphism of $L$, and let $b$ be a natural number coprime to $p$ with $s\zeta = \zeta^{b}$. Let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(Mp)$ with upper-left entry $\delta_{00} \equiv b \pmod p$ and $\delta_{00} \equiv 1 \pmod M$, and let $n$ be a natural number. Then there exists $z \in L$ such that $\iota z$ is the $n$-th coefficient of the period-$1$ $q$-expansion of $\tau \mapsto (f \mid_k \gamma)(\,\mathrm{diag}(p,1)\cdot\tau\,)$, where $\mathrm{diag}(p,1)$ is [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21), the upper-triangular element $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{R})$, and such that the $n$-th coefficient of the period-$1$ $q$-expansion of $\tau \mapsto ((f \mid_k \delta) \mid_k \gamma)(\,\mathrm{diag}(p,1)\cdot\tau\,)$ equals $\iota(s z)$.
--
--   This is the statement that the Galois conjugate, by an automorphism sending $\zeta \mapsto \zeta^{b}$, of the Fourier expansion of the Atkin–Lehner shifted form $(f\mid_k\gamma)(p\tau)$ is computed by the diamond operator $\langle \delta \rangle$ acting through $\delta \in \Gamma_0(Mp)$; the rationality of the coefficients is recorded by the existence of $z \in L$ with $\iota z$ the given coefficient. It is phrased for an arbitrary abstract $p$-th cyclotomic field $L$ together with a complex embedding $\iota$, so that it can be applied inside function fields of the modular curve over $L$; it is used in the construction of the level-$p$ involution on the function field of $X_1(Mp)$, through [`ModularCurve.XOneP.ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul`](thm.html#ModularCurve.XOneP.ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Even k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (ι : L →+* ℂ) (s : L ≃ₐ[ℚ] L) (b : ℕ) (hb : Nat.Coprime b p) (hs : s ζ = ζ ^ b)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδp : ((δ 0 0 : ℤ) : ZMod p) = (b : ZMod p)) (hδM : ((δ 0 0 : ℤ) : ZMod M) = 1) (n : ℕ) :
    ∃ z : L, ι z = (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∧
      (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n = ι (s z) := by sorry
