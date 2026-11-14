-- Prove2me | Theorems.Thm_LatticePrepro_FixedSystem_recover
-- name    : LatticePrepro.FixedSystem.recover
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:39.69119+00:00
-- url     : https://prove2.me/theorems/37c7a763-cb0d-467a-96b9-c48a655cafde
-- title:
--   Lemma 4.7 (pointwise form) — recovering a valid Boolean assignment at a support point
-- statement:
--   Let $p$ be a prime, $K$ a field that is an $\mathbb{F}_p$-algebra, and $\Omega$ an extension field of $K$. Elements of $\mathbb{F}_p$ and $K$ are viewed in $\Omega$ through the algebra maps. Let $V$ be a quadratic verifier over $\mathbb{F}_p$ with coordinates $0,\dots,S$ and gate coefficients $c^{(b)}_{i,j}$, and let $E_0=0,E_1,\dots,E_S\in K$ be an encoding tuple, with $E_1,\dots,E_S$ linearly independent over $\mathbb{F}_p$. Let $F_{i,j}\in\mathbb{F}_p$ ($0\le i,j\le S$) and $\alpha\in\Omega$ satisfy:
--
--   1. $F_{i,j}=F_{j,i}$ and $F_{i,i}=F_{i,0}$ for all $i,j$;
--   2. the encoding identities $\alpha\cdot F_{0,j}=\sum_{i=0}^SE_i\,F_{i,j}$ in $\Omega$, for every $j$;
--   3. the gate identities $\sum_{i,j=0}^Sc^{(b)}_{i,j}F_{i,j}=0$ in $\mathbb{F}_p$, for every gate $b$;
--   4. $F_{0,0}\ne0$.
--
--   Then there is an assignment $z\in\mathbb{F}_p^{S+1}$ with $z_0=1$ and $z_i\in\{0,1\}$ for all $i$, which is valid, i.e. $\sum_{i,j}c^{(b)}_{i,j}z_iz_j=0$ for every gate $b$, and which encodes $\alpha$:
--   $$\sum_{i=0}^Sz_i\,E_i=\alpha.$$
--
--   In the paper, Lemma 4.7 is stated for functions $F_{i,j}$ on a finite set of points. This is its pointwise version at a single point $\alpha$, with $F_{i,j}=F_{i,j}(\alpha)$. In the soundness part of Theorem 4.6 it is applied at a point where the main coefficient function is nonzero, which yields an accepting computation.
--
--   **Formalization Note** The Lean statement assumes $F_{0,0}\ne0$, whereas the paper derives $F_{0,0}(\alpha)\neq0$ from any nonzero $F_{i,j}(\alpha)$. It concludes existence of $z$ but not its uniqueness, and it does not record the paper's identity $F_{i,j}=F_{0,0}z_iz_j$. Because $E_0=0$, sums over $i$ may start at $0$. "Boolean with $z_0=1$" is `IsBooleanAssignment` and validity is `IsValid`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 4.7 (\label{lem:exact-validity}), pointwise form; Lean: LatticePrepro/Reduction/Soundness.lean, LatticePrepro.FixedSystem.recover

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

theorem LatticePrepro.FixedSystem.recover {Fv : Fin (V.S + 1) → Fin (V.S + 1) → ZMod p}
    (hsymm : ∀ i j, Fv i j = Fv j i) (hdiag : ∀ i, Fv i i = Fv i 0) {α : Ω}
    (henc : ∀ j, α * algebraMap (ZMod p) Ω (Fv 0 j) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (Fv i j))
    (hgate : ∀ b, ∑ i, ∑ j, V.coeff b i j * Fv i j = 0) (hne : Fv 0 0 ≠ 0) :
    ∃ z : Fin (V.S + 1) → ZMod p, V.IsBooleanAssignment z ∧ V.IsValid z ∧
      algebraMap K Ω (ε.enc z) = α := by sorry
