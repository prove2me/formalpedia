-- Prove2me | Theorems.Thm_FrobeniusEndo_galoisTrace_frob_eq_of_line_of_charEqOnPoints
-- name    : FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/7c6f32d8-2eb1-5911-9c38-1c1a619d385f
-- title:
--   Frobenius trace on W[p] as q+1-#W(mathbb F_q)
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field of cardinality $q=\#F$, and $k$ a field, with $R$-algebra structures on $F$ and $k$ and an $F$-algebra structure on $k$ forming a scalar tower. Let $W$ be a Weierstrass curve over $R$, and let $\sigma$ be an $F$-algebra automorphism of $k$ with $\sigma x = x^{q}$ for every $x \in k$; $\sigma$ acts on the group $(W⁄k).\mathrm{Point}$ of points of the base change of $W$ to $k$, and `frobEnd W σ` is the corresponding additive endomorphism. Let $p$ be a prime such that the $p$-torsion subgroup of $(W⁄k).\mathrm{Point}$ has cardinality $p^{2}$ and such that $p \neq 0$ in $k$. Let $a$ be an integer subject to two hypotheses: for every $m \geq 1$ with $m \neq 0$ in $k$, the kernel of $m \cdot \mathrm{id} - \sigma$ on $(W⁄k).\mathrm{Point}$ has cardinality $m^{2} - am + q$, and this cardinality is nonzero; and for every point $P$ of $(W⁄k).\mathrm{Point}$ one has $\sigma(\sigma P) - a\,(\sigma P) + q\,P = 0$. The conclusion is twofold: the trace over $\mathbb{Z}/p$ of the endomorphism induced by $\sigma$ on the $p$-torsion submodule of $(W⁄k).\mathrm{Point}$ equals $q + 1 - \#(W⁄F).\mathrm{Point}$ in $\mathbb{Z}/p$, and its determinant equals $q$ in $\mathbb{Z}/p$.
--
--   This is the Eichler–Shimura shape of the Frobenius data on $p$-torsion over a finite field: the trace of $\mathrm{Frob}_q$ on $W[p]$ is $q+1-\#W(F)$ and its determinant is $q$, both modulo $p$, with no restriction on $p$ beyond $p \neq \operatorname{char} k$. It feeds the computation of traces and determinants of Galois representations over algebraically closed fields, which in turn supplies the congruence $\operatorname{tr}\bar\rho_{E,p}(\mathrm{Frob}_\ell) \equiv a_\ell$, $\det \equiv \ell \pmod p$ used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_galoisTrace_frob_eq_of_line_of_charEqOnPoints.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point p) = p ^ 2) (hpk : (p : k) ≠ 0) (a : ℤ) (hline : ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + Fintype.card F) (hpos : ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hpt : FrobCharEqOnPoints W σ a (Fintype.card F)) : galoisTrace F W p σ = (Fintype.card F : ZMod p) + 1 - (Nat.card (W⁄F).Point : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd F W p σ) = (Fintype.card F : ZMod p) := by sorry
