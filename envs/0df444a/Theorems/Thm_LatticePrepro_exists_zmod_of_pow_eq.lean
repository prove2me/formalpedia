-- Prove2me | Theorems.Thm_LatticePrepro_exists_zmod_of_pow_eq
-- name    : LatticePrepro.exists_zmod_of_pow_eq
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:54.143588+00:00
-- url     : https://prove2.me/theorems/afed7807-7eca-4a51-8e63-1b95ca6a9244
-- title:
--   Fixed points of Frobenius lie in the prime field
-- statement:
--   Let $p$ be a prime and let $\Omega$ be a field that is an algebra over the prime field $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$, with structure map $\iota\colon \mathbb{F}_p \to \Omega$ (so $\Omega$ has characteristic $p$). If an element $c \in \Omega$ is fixed by the Frobenius map, then it comes from the prime field:
--   $$c^p = c \quad\Longrightarrow\quad c = \iota(a) \ \text{ for some } a \in \mathbb{F}_p.$$
--
--   In the moment reconstruction theorem (Theorem A.7), the coefficients of the reconstructed coefficient function are shown to be fixed by Frobenius; this lemma then places them in $\mathbb{F}_p$, so that the reconstructed function takes values in the prime field, as coefficient functions must (Definition 4.1).
--
--   **Formalization Note**: $\mathbb{F}_p$ is `ZMod p` with `Fact p.Prime`, and $\iota$ is `algebraMap (ZMod p) Ω`. The field $\Omega$ is arbitrary; it need not be finite (in the application it is an algebraic closure).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Theorem A.7 (\label{thm:moment-hankel-reconstruction}); Lean: LatticePrepro/Basic/FiniteField.lean, LatticePrepro.exists_zmod_of_pow_eq

import Mathlib

open Polynomial
variable {Ω : Type*} [Field Ω]

theorem LatticePrepro.exists_zmod_of_pow_eq {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) Ω] {c : Ω}
    (hc : c ^ p = c) : ∃ a : ZMod p, algebraMap (ZMod p) Ω a = c := by sorry
