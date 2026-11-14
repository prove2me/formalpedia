-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_enc_assignOf
-- name    : LatticePrepro.QuadraticVerifier.enc_assignOf
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:17.254973+00:00
-- url     : https://prove2.me/theorems/070d9640-4b14-4bcf-a26c-b26d27ceac6a
-- title:
--   Encodings of assignments with prefix $(x,1)$: $\mathrm{enc}(z) = \theta_x + \sum_{i > n+1} z_i E_i$
-- statement:
--   Let $V$ be a quadratic verifier over $\mathbb{F}_p$ ($p$ prime) with $n$ input coordinates and $S$ assignment coordinates, let $K$ be a field that is an $\mathbb{F}_p$-algebra, and let $E = (E_0 = 0, E_1, \dots, E_S)$ be an encoding tuple in $K$. For an instance $x \in \{0,1\}^n$ and values $u = (u_i)_{n+1 < i \le S}$ in $\mathbb{F}_p$ on the auxiliary coordinates, let $z = \mathrm{assignOf}(x, u) = (1, x_1, \dots, x_n, 1, u_{n+2}, \dots, u_S)$. Then
--   $$\mathrm{enc}(z) = \sum_{i=0}^{S} z_i E_i = \theta_x + \sum_{i=n+2}^{S} u_i\, E_i,$$
--   where $\theta_x = \sum_{i=1}^{n} x_i E_i + E_{n+1}$ is the instance encoding.
--
--   In the soundness proof of Theorem 4.6, this identity shows that the encodings of assignments over $\mathbb{F}_p$ with prefix $(x, 1)$ form the coset $\theta_x + T$, where $T = \operatorname{span}_{\mathbb{F}_p}\{E_i : i > n+1\}$; summing the translation identity over this coset produces an accepting computation on $x$.
--
--   **Formalization Note**: Instances are `Fin n → Bool` with bits stored as $0/1 \in \mathbb{F}_p$, the auxiliary values $u$ are a function on `AuxIdx` (the coordinates $i$ with $n+1 < i$), and the last sum runs over `AuxIdx`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the soundness proof of Theorem 4.6 (\label{thm:fixed-verifier-reduction}); Lean: LatticePrepro/Verifier/Quadratic.lean, LatticePrepro.QuadraticVerifier.enc_assignOf

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)

theorem LatticePrepro.QuadraticVerifier.enc_assignOf (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    ε.enc (V.assignOf x u) = V.instanceEnc ε x + ∑ i : V.AuxIdx, u i • ε.E i.1 := by sorry
