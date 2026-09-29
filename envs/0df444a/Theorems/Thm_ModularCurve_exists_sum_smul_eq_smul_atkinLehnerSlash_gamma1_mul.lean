-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
-- name    : ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/432e51b9-5a4c-559a-8864-a8491f2aba2b
-- title:
--   Atkin–Lehner translate spans ℚ(ζₚ)-combinations of integral forms
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $p \nmid M$, and let $k$ be an integer. Let $f$ be a modular form of weight $k$ for the subgroup $\Gamma_1(Mp)$ of $\mathrm{GL}_2(\mathbb{R})$, and suppose $f$ has integral $q$-expansion in the sense of [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37): there is a power series $p_0$ over $\mathbb{Z}$ whose coefficientwise image in $\mathbb{C}$ is the width-$1$ $q$-expansion of $f$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{11}$ (the lower right entry, in zero-based indexing $\gamma\,1\,1$). Then there exist a nonzero integer $D$, a natural number $n$, scalars $c : \mathrm{Fin}\,n \to \mathbb{C}$, modular forms $F_i$ of weight $k$ for $\Gamma_1(Mp)$ and power series $r_i$ over $\mathbb{Z}$ such that every $c_i$ lies in the subfield $\mathbb{Q}(e^{2\pi i/p})$ of $\mathbb{C}$ generated over $\mathbb{Q}$ by $\exp(2\pi i/p)$, each $F_i$ has integral $q$-expansion with associated integer power series $r_i$, and, as functions on the upper half plane, $$D \cdot \bigl(\tau \mapsto (f \mid_k \gamma)(\mathrm{heckeDiagMatrix}(p) \cdot \tau)\bigr) = \sum_i c_i F_i,$$ where $\mathrm{heckeDiagMatrix}(p)$ is the element of $\mathrm{GL}_2(\mathbb{R})$ given by the matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$, so that the argument is $p\tau$.
--
--   This is the arithmetic input for the Atkin–Lehner involution at $p$ on $X_1(Mp)$: the function $\tau \mapsto (f\mid_k\gamma)(p\tau)$, which up to a power of $p$ is the image of $f$ under $W_p$, is expressed as a $\mathbb{Q}(\zeta_p)$-linear combination of weight-$k$ forms on $\Gamma_1(Mp)$ with integral $q$-expansions, whence the involution is defined over $\mathbb{Q}(\zeta_p)$ on the model in which the cusp $\infty$ is rational. It is used in the construction of the $q$-expansion and Atkin–Lehner data attached to the curves $X_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ)
      (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      D ≠ 0 ∧
      (∀ i, c i ∈ IntermediateField.adjoin ℚ
        ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)) ∧
      (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧
      ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))
        = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ) := by sorry
