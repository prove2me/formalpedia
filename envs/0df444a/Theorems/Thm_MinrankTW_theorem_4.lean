-- Prove2me | Theorems.Thm_MinrankTW_theorem_4
-- name    : MinrankTW.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:06.551907+00:00
-- url     : https://prove2.me/theorems/e372dc46-5ed6-4429-a56c-4fd6b8106b94
-- title:
--   Theorem 4 ([PW26, Theorem 1]) — subspace zeta transforms and inverses in $O_q(d^2N_q(d))$ operations
-- statement:
--   Let $p$ be the characteristic of $\mathbb F_q$. For weights $f(S)$ in a commutative ring in which $p$ is invertible, the subspace zeta transform
--   $$
--   (Zf)(R)=\sum_{S\le R}f(S),\qquad R\le\mathbb F_q^d,
--   $$
--   and its inverse can each be computed in $O_q(d^2N_q(d))$ arithmetic operations. The same bound holds for the transpose $(Z^{\mathsf T}f)(R)=\sum_{S\ge R}f(S)$ and its inverse.
--
--   The theorem is proved in the companion paper [PW26] and quoted on p.8; it is what brings the join from $N_q(b)^2$ to $N_q(b)\,\mathrm{poly}(b)$ operations.
--
--   **Formalization Note** There is a constant $C$ depending only on $\mathbb F_q$ such that for every $d\ge0$ four straight-line programs, each with at most $Cd^2N_q(d)$ arithmetic gates, compute $Zf$, $Z^{-1}f$, $Z^{\mathsf T}f$ and $(Z^{\mathsf T})^{-1}f$ over every commutative ring with an element $p^{-1}$ satisfying $p\cdot p^{-1}=1$. An inverse program $P$ is specified by $Z(Pf)=f$.
--
--   Differences from the source:
--   - encoding: "computed in O_q(d²N_q(d)) arithmetic operations" → straight-line programs (one per d) with at most C·d²·N_q(d) arithmetic gates, C depending only on F; reason: the arithmetic-operation model of the source; O_q as a constant depending on q
--   - encoding: the inverse transform → a program P with Z(P f) = f for all f; reason: Z is invertible, so this pins P f = Z⁻¹f
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 4 (= [PW26, Theorem 1]), p.8

import Mathlib
import Definitions.Def_MinrankTW_Nq
import Definitions.Def_MinrankTW_tableMap
import Definitions.Def_MinrankTW_zetaKer
import Definitions.Def_MinrankTW_SLP

namespace MinrankTW

/-- **Theorem 4** (Fast subspace summation, \[PW26, Theorem 1\]), as stated in Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.8. Let
`p` be the characteristic of `F_q`. For weights `f(S)` in a commutative ring in which `p` is
invertible, the subspace zeta transform `(Zf)(R) = ∑_{S ≤ R} f(S)` (`R ≤ F_q^d`) and its inverse
can each be computed in `O_q(d² N_q(d))` arithmetic operations; the same bound holds for the
transpose, which sums over superspaces, and its inverse.

**Formalization Note** For each `d` there are four straight-line programs (inputs and
outputs indexed by the subspaces of `F^d`), each with at most `C d² N_q(d)` operations, `C`
depending only on `F`, which compute `Z f`, `Z⁻¹ f`, `Zᵀ f`, `(Zᵀ)⁻¹ f` over every
commutative ring with an inverse `pinv` of `p`. An inverse program is specified by
`Z (P f) = f` (`Z` is invertible). At `d = 0` every transform is the identity on the
single subspace, computed by one (free) input gate, so the bound `0` holds there too. The proof is in the companion paper \[PW26\]. -/
theorem theorem_4 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℕ, ∀ d : ℕ,
      ∃ PZ PZinv PZt PZtinv : SLP (Submodule F (Fin d → F)) (Submodule F (Fin d → F)),
        PZ.WellFormed ∧ PZinv.WellFormed ∧ PZt.WellFormed ∧ PZtinv.WellFormed ∧
        PZ.cost ≤ C * d ^ 2 * Nq F d ∧ PZinv.cost ≤ C * d ^ 2 * Nq F d ∧
        PZt.cost ≤ C * d ^ 2 * Nq F d ∧ PZtinv.cost ≤ C * d ^ 2 * Nq F d ∧
        ∀ (A : Type) [CommRing A] (pinv : A), (ringChar F : A) * pinv = 1 →
          ∀ f : Submodule F (Fin d → F) → A,
            PZ.eval pinv f = tableMap zetaKer f ∧
            tableMap zetaKer (PZinv.eval pinv f) = f ∧
            PZt.eval pinv f = tableMap (fun R S => zetaKer S R) f ∧
            tableMap (fun R S => zetaKer S R) (PZtinv.eval pinv f) = f := by sorry

end MinrankTW
