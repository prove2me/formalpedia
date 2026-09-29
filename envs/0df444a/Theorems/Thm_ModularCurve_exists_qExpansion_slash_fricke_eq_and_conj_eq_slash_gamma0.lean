-- Prove2me | Theorems.Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
-- name    : ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/1125fdad-f209-564e-bde6-0e9bbf1e289a
-- title:
--   Galois action on the Fricke transform's q-expansion
-- statement:
--   Let $M$ be a nonzero natural number and $k$ an integer, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume that every coefficient of the $q$-expansion of $f$ of width $1$ (that is, in the parameter $q = e^{2\pi i \tau}$) is the image of a rational number under $\mathbb{Q} \to \mathbb{C}$. Fix a ring homomorphism $\iota \colon \overline{\mathbb{Q}} \to \mathbb{C}$ from an algebraic closure of $\mathbb{Q}$, and let $W \in \mathrm{GL}_2(\mathbb{R})$ be an element whose underlying matrix is $\begin{pmatrix} 0 & -1 \\ M & 0\end{pmatrix}$. Then there is a sequence $(a_n)_{n \ge 0}$ of elements of $\overline{\mathbb{Q}}$ such that, first, for every $n$ the $n$-th coefficient of the width-$1$ $q$-expansion of $f \mid_k W$ (the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$ on functions on the upper half-plane) equals $\iota(a_n)$; and second, for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every natural number $c$ with $\sigma(\zeta) = \zeta^{c}$ for all $\zeta \in \overline{\mathbb{Q}}$ satisfying $\zeta^{M} = 1$, and for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ whose lower right entry reduces to $c$ in $\mathbb{Z}/M$, the $n$-th coefficient of the width-$1$ $q$-expansion of $(f \mid_k W) \mid_k \gamma$ equals $\iota(\sigma(a_n))$ for every $n$.
--
--   This is Shimura's reciprocity law at the Fricke matrix $W_M$ in the form needed here: the Fourier coefficients of the Fricke transform of a $q$-rational form on $\Gamma_1(M)$ are algebraic, and the Galois action on them is realised by the diamond operators, $\sigma$ acting through the residue $c$ by which it raises $M$-th roots of unity. It is used in the construction of the Fricke-twisted function field with its Galois action and in the expression of $f \mid_k W$ as a combination of forms with controlled coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n =
        ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 1 1 : ℤ) : ZMod M) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
            (((⇑f : UpperHalfPlane → ℂ) ∣[k] W) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n = ι (σ (a n)) := by sorry
