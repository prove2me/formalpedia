-- Prove2me | Theorems.Thm_GRH_corrected_prime_ramp_changeLevel_le
-- name    : GRH.corrected_prime_ramp_changeLevel_le
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:41:52.184261+00:00
-- url     : https://prove2.me/theorems/60a4b79d-8156-4c67-959f-c0390ef016ad
-- title:
--   Uniform corrected prime-ramp error under change of modulus
-- statement:
--   Fix a modulus $qge 1$ and $0<	hetale 1$. Write the corrected real ramp of a nonprincipal Dirichlet character $chi$ as
--   $$G_chi(y)=sum_{1le nle y} Lambda(n)operatorname{Re}chi(n)(y/n-1)_+ + yoperatorname{Re}rac{L'(1,chi)}{L(1,chi)}.$$
--   There is a constant $C(q,	heta)ge0$ such that for every divisor $dmid q$, every nonprincipal character $psimod d$ and its lift $chimod q$, and every $yge1$,
--   $$|G_chi(y)-G_psi(y)|le C(q,	heta)y^	heta.$$
--   The constant is uniform in the inducing modulus and the character. This estimate carries a one-sided window bound from the primitive character to every character it induces.
-- source:
--   Dirichlet L-function change-of-modulus comparison for the corrected ramp in Levent Alpöge, 20 November 2026, https://alpo.ge/remark.pdf.

import Mathlib

open Finset ArithmeticFunction Set

namespace GRH

theorem corrected_prime_ramp_changeLevel_le (q : ℕ) [NeZero q] (θ : ℝ)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    let R := fun (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ) =>
      (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod k)).re * max (y/(n:ℝ)-1) 0) +
          y * (deriv χ.LFunction 1 / χ.LFunction 1).re
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) [NeZero d] (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d),
      ψ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
        |R q (DirichletCharacter.changeLevel hdq ψ) y - R d ψ y| ≤ C*y^θ := by sorry

end GRH
