-- Prove2me | Theorems.Thm_HarlowTASI_erasure_correction_tfae
-- name    : HarlowTASI.erasure_correction_tfae
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:12:01.089126+00:00
-- url     : https://prove2.me/theorems/e7ee5d33-2dd9-455d-80e3-fc3635ef34db
-- title:
--   Theorem 4.1 — four equivalent characterizations of a correctable erasure
-- statement:
--   Let $\mathcal H=\mathcal H_R\otimes\mathcal H_{\overline R}$ be finite-dimensional and let $\mathcal H_{code}\subseteq\mathcal H$ be a nonzero subspace with orthonormal basis $|\tilde i\rangle$, $i\in C$, and orthogonal projection $P$. The following are equivalent:
--
--   1. For every operator $\tilde O$ on $\mathcal H_{code}$ there is an operator $O_R$ on $\mathcal H_R$ such that for all $|\tilde\psi\rangle\in\mathcal H_{code}$
--   $$O_R|\tilde\psi\rangle=\tilde O|\tilde\psi\rangle,\qquad O_R^\dagger|\tilde\psi\rangle=\tilde O^\dagger|\tilde\psi\rangle. \tag{4.16}$$
--   2. For every operator $X_{\overline R}$ on $\mathcal H_{\overline R}$ there is $\lambda\in\mathbb C$ with $PX_{\overline R}P=\lambda P$. (4.17)
--   3. With a reference system $S$ of dimension $|S|=\dim\mathcal H_{code}$ and $|\phi\rangle=|S|^{-1/2}\sum_i|i\rangle_S|\tilde i\rangle_{R\overline R}$ (4.18), one has $\rho_{S\overline R}(\phi)=\rho_S(\phi)\otimes\rho_{\overline R}(\phi)$. (4.19)
--   4. $|S|\le|R|$, and for a decomposition $\mathcal H_R=(\mathcal H_{R_1}\otimes\mathcal H_{R_2})\oplus\mathcal H_{R_3}$ with $|R_1|=|S|$ and $|R_3|<|S|$ there are a unitary $U_R$ on $\mathcal H_R$ and a state $|\chi\rangle_{R_2\overline R}$ such that
--   $$|\tilde i\rangle_{R\overline R}=U_R\big(|i\rangle_{R_1}|\chi\rangle_{R_2\overline R}\big).\tag{4.20}$$
--
--   Theorem 4.1 is the basic structure theorem for erasure codes: condition (1) says that the encoded information can be reconstructed on $R$, and (4) exhibits the encoding circuit. It is the subsystem-code special case of the mechanism behind Theorem 5.2, and it is the input of the quantum Singleton bound (4.25).
--
--   **Formalization Note** $\mathcal H_{code}$ is given by an isometry $V$ (columns $|\tilde i\rangle=V|i\rangle$), operators by matrices, and $O_R$ acts as $O_R\otimes I_{\overline R}$. The code subspace is assumed nonzero (the lectures implicitly assume it: condition (4) requires $|R_3|<|S|$ and (4.18) normalizes by $|S|^{-1/2}$). In (4), $|R_2|=\lfloor|R|/|S|\rfloor$ and $|R_3|=|R|\bmod|S|$ are forced, and the statement is required for every identification of the basis of $\mathcal H_R$ with $(R_1\times R_2)\sqcup R_3$; $|\chi\rangle$ is required to be a unit vector.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §4.3, pp. 28–29, Theorem 4.1, eqs. (4.16)–(4.20).

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix
open scoped Kronecker

namespace HarlowTASI
theorem erasure_correction_tfae {R Rb C : Type} [Fintype R] [DecidableEq R] [Fintype Rb]
    [DecidableEq Rb] [Fintype C] [DecidableEq C] [Nonempty C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V) :
    List.TFAE
      [ ∀ O : Matrix C C ℂ, ∃ OR : Matrix R R ℂ,
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ,
        ∀ X : Matrix Rb Rb ℂ, ∃ c : ℂ,
          (V * Vᴴ) * ((1 : Matrix R R ℂ) ⊗ₖ X) * (V * Vᴴ) = c • (V * Vᴴ),
        reducedSB (codeReferenceState V) =
          reducedS (codeReferenceState V) ⊗ₖ reducedB (codeReferenceState V),
        Fintype.card C ≤ Fintype.card R ∧
          ∀ e : R ≃ (C × Fin (Fintype.card R / Fintype.card C)) ⊕
              Fin (Fintype.card R % Fintype.card C),
            ∃ UR : Matrix R R ℂ, IsUnitaryMatrix UR ∧
              ∃ χ : Fin (Fintype.card R / Fintype.card C) × Rb → ℂ,
                ∑ x, ‖χ x‖ ^ 2 = 1 ∧
                ∀ (i : C) (r : R) (b : Rb),
                  V (r, b) i = ∑ r', UR r r' *
                    (match e r' with
                      | Sum.inl (c, k) => if c = i then χ (k, b) else 0
                      | Sum.inr _ => 0) ] := by sorry
end HarlowTASI
