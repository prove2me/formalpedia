-- Prove2me | Theorems.Thm_ModFormPIR_fact_10_11
-- name    : ModFormPIR.fact_10_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:49.147543+00:00
-- url     : https://prove2.me/theorems/85f3391e-c900-465b-9195-c7d42b83fee6
-- title:
--   Fact 10.11, p.41 — the Weil representation of $SL_2(\mathbb Z)$
-- statement:
--   Let $q$ be an odd prime and $\mu\not\equiv0\pmod q$. There is a unique representation $\rho$ of $SL_2(\mathbb Z)$ on $\mathbb C^q$ with $\rho(T)=\rho_T$ and $\rho(S)=\rho_S$. Moreover, $\rho(g)=I$ for every $g\in\Gamma(q)$, and for every $g=\begin{pmatrix}a&b\\c&d_0\end{pmatrix}\in\Gamma_0(q)$ and $x\in\mathbb Z_q$,
--   $$\rho(g)e_x=\Big(\frac aq\Big)\zeta_q^{\mu bd_0x^2}e_{d_0x}.$$
--
--   $\Theta$ transforms under this representation, and the monomial form on $\Gamma_0(q)$ is the source of the explicit matrices at the selected cusps.
--
--   Differences from the source:
--   - encoding: a representation into GL_q(ℂ) → a monoid homomorphism into q × q matrices; reason: on a group its values are invertible
--   - encoding: "ρ(g) depends only on the reduction of g modulo q" → omitted as a separate clause; ρ(g) = I on Γ(q) is stated; reason: it is the printed consequence of triviality on the normal subgroup Γ(q)
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Fact 10.11, p.41 (PDF p.45), citing Strömberg, Weil representations associated with finite quadratic modules, Math. Z. 2013

import Mathlib
import Definitions.Def_ModFormPIR_Weil

open Matrix
open scoped MatrixGroups

set_option autoImplicit false

namespace ModFormPIR

/-- **Fact 10.11** (The Weil representation), p.41. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For `μ ≢ 0 (mod q)` there is a unique representation `ρ` of `SL₂(ℤ)` on `ℂ^q` with `ρ(T) = ρ_T`, `ρ(S) = ρ_S`. It is trivial on `Γ(q)`, and for `g = [a b; c d₀] ∈ Γ₀(q)`,
`ρ(g) e_x = (a/q) ζ_q^{μbd₀x²} e_{d₀x}`, (20).

**Formalization Note.** A monoid homomorphism into `q × q` matrices: being on a group, its values are invertible, so this is a map into `GL_q(ℂ)`. `(a/q)` is Mathlib's `legendreSym`. -/
theorem fact_10_11 (q : ℕ) [Fact q.Prime] (hodd : Odd q) (μ : ℤ) (hμ : (μ : ZMod q) ≠ 0) :
    (∃! ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ, IsWeil q μ ρ) ∧
    ∀ ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ, IsWeil q μ ρ →
      (∀ g ∈ CongruenceSubgroup.Gamma q, ρ g = 1) ∧
      ∀ g ∈ CongruenceSubgroup.Gamma0 q, ∀ x : ZMod q,
        (ρ g).mulVec (Pi.single x 1) =
          ((legendreSym q (g 0 0 : ℤ) : ℤ) : ℂ) •
            zq q ((μ : ZMod q) * ((g 0 1 : ℤ) : ZMod q) * ((g 1 1 : ℤ) : ZMod q) * x ^ 2) •
              (Pi.single (((g 1 1 : ℤ) : ZMod q) * x) 1 : ZMod q → ℂ) := by sorry

end ModFormPIR
