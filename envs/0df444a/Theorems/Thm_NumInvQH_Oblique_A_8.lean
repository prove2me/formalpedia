-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_8
-- name    : NumInvQH.Oblique.A_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:33.461457+00:00
-- url     : https://prove2.me/theorems/6b86d240-e375-4c27-947b-e06c103cba45
-- title:
--   Eq. (A.8) and $JCJ=J$ — $JC=(C^{1/2}M)^{+}C^{1/2}$, proof of Theorem A.4(1) (p. 26; identity announced p. 25)
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $C\in\mathbb R^{n\times n}$ be symmetric positive semidefinite with positive semidefinite square root $C^{1/2}$ (so $C^{1/2}C^{1/2}=C$), let $A\in\mathbb R^{k\times n}$, $M=I-A^{+}A$, $J=(MCM)^{+}$. Then
--
--   $$JC=MJMC=M(C^{1/2}M)^{+}C^{1/2}=(C^{1/2}M)^{+}C^{1/2},\qquad JCJ=J.$$
--
--   Identity (A.8) shows that $JC$ is the oblique projector $U(VU)^{+}V$ with $U=M$, $V=C^{1/2}$ hidden behind the pseudoinverse $J$; the identity $JCJ=J$ is what turns the minimizer of Proposition A.3 into formula (A.5).
--
--   **Formalization Note** $C^{1/2}$ is an explicit matrix $R$ with hypotheses $R\succeq0$ and $RR=C$ (the unique positive semidefinite square root). The middle expression $M((C^{1/2}M)^{\mathsf T}C^{1/2}M)^{+}MC^{1/2}C^{1/2}$ of the printed chain equals $MJMC$ by definition of $J$ and is not repeated. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 26, eq. (A.8), proof of Theorem A.4(1); p. 25 (identity JCJ = J)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Equation (A.8) in the proof of Theorem A.4(1), together with the identity `JCJ = J`
announced before Theorem A.4. `R` is the positive semidefinite square root `C^{1/2}` of `C`. -/
theorem A_8 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosSemidef) (hRC : R * R = C)
    (Ap : Matrix (Fin n) (Fin k) ℝ)
    (hAp : LocalDistanceNetwork.IsMoorePenroseInverse A Ap)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse ((1 - Ap * A) * C * (1 - Ap * A)) J)
    (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : LocalDistanceNetwork.IsMoorePenroseInverse (R * (1 - Ap * A)) K) :
    let M := 1 - Ap * A
    J * C = M * J * M * C ∧
      J * C = M * K * R ∧
      J * C = K * R ∧
      J * C * J = J := by sorry

end NumInvQH.Oblique
