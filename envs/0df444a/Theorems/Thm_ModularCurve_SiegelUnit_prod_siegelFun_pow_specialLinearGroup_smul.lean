-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul
-- name    : ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/3d70cdac-9fd5-54c4-80bc-1e5a3757b5d3
-- title:
--   SL₂(ℤ)-transport and Γ₁(N)-invariance of Siegel-function power products
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $e \colon \mathbb{Z}/N \times \mathbb{Z}/N \to \mathbb{N}$ be an arbitrary exponent function. For integers $r,s$ and $z \in \mathbb{C}$, `siegelFun N r s z` denotes the Siegel function of level $N$ and characteristic $(r,s)$, namely $-\exp(\pi i s(r-N)/N^2)\,\exp\bigl(\pi i((r/N)^2 - r/N + 1/6)z\bigr)\,(1 - q_z)$ times the infinite product $\prod_{n \ge 0}(1 - e^{2\pi i z(n+1)}q_z)(1 - e^{2\pi i z(n+1)}q_z^{-1})$, where $q_z = \exp(2\pi i(rz+s)/N)$; the index pair $(r,s) \in (\mathbb{Z}/N)^2$ is always fed in through the least non-negative representatives $r.\mathrm{val}, s.\mathrm{val}$. The theorem asserts two things at once. First, for every $\beta \in \mathrm{SL}_2(\mathbb{Z})$ and every $\tau$ in the upper half-plane, $\prod_{r,s} g_{r,s}(\beta\tau)^{12Ne(r,s)}$ equals $\prod_{r,s} g_{r',s'}(\tau)^{12Ne(r,s)}$, where $r'$ and $s'$ are the reductions modulo $N$ of $r\beta_{00} + s\beta_{10}$ and $r\beta_{01} + s\beta_{11}$, again lifted by `val`; this is an exact equality of complex numbers, with no root-of-unity ambiguity. Second, if $e$ satisfies $e(r, s+r) = e(r,s)$ for all $r,s$, then for every $\gamma \in \Gamma_1(N)$ (Mathlib's `CongruenceSubgroup.Gamma1 N`) and every $\tau$, the same product is unchanged by $\tau \mapsto \gamma\tau$.
--
--   The products $u_e = \prod_{r,s} g_{r,s}^{12Ne(r,s)}$ with exponents constant along the orbits $s \mapsto s + r$ are the classical modular units on $X_1(N)$ in the sense of Kubert and Lang, and the first assertion is the transport law $u_e \circ \beta = u_{e \circ \beta^{-1}}$ in the form needed to read off the behaviour of $u_e$ at an arbitrary cusp. It is used in the construction of modular forms on $\Gamma_1(N)$ with prescribed integral $q$-expansions and integrality properties under slash operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups in

theorem ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) :
    (∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
              (τ : ℂ) ^ (12 * N * e r s)) ∧
    ((∀ r s : ZMod N, e r (s + r) = e r s) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma1 N →
        ∀ τ : UpperHalfPlane,
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
            ∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) := by sorry
