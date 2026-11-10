-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_nogood_oracle
-- name    : NogoodColoring1137.Main.nogood_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:03:49.49317+00:00
-- url     : https://prove2.me/theorems/fb5ca9d1-ce1e-43aa-8b63-196e27d0f97f
-- title:
--   Theorem 2 — Polynomial-time nogoods on every prescribed scope
-- statement:
--   Let $G$ have $n\ge8$ vertices and diameter at most two. One uniform finite program computes, on every specified set $U$ of size $\ell=5\lceil\log_4(n+1)\rceil-2$, an assignment $s:U\to\{0,1,2\}$ satisfying
--   $$\nexists C\in\mathcal C(G),\quad C|_U=s.$$
--   Uniform positive polynomial constants bound bit runtime independently of the graph and queried scope. No local properness or list-respect requirement is imposed on the nogood. This supplies the application's oracle on every prescribed subset.
--
--   **Formalization Note** The exact coefficient 5 and subtraction 2 use Nat.clog. The proof p.18 gives $O(n^2\log n)$ adjacency-matrix work; polynomial bit time has unspecified uniform implementation constants, with no invented numerical coefficient.
--
--   Differences from the source:
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Theorem 2, p.14; proof pp.16–18

import Definitions.Def_NogoodColoring1137_Main_DomainEncoding
import Definitions.Def_NogoodColoring1137_Main_Folds

namespace NogoodColoring1137.Main

/-- Theorem 2, pp.14,16–18. Constants and finite program are uniform in the queried scope. -/
theorem nogood_oracle :
    ∃ (P : IntMul.MultitapeTM) (c e : ℕ), 0 < c ∧
    ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj),
      8 ≤ n → DiameterTwo G → ∀ U : Finset (Fin n), U.card = NogoodLength n →
      ∃ s : U → Color,
        (¬ ∃ C ∈ @Solutions n G adj (FullLists n), ∀ v : U, C v.val = s v) ∧
        Runs P (@EncodeGraph n G adj ++ EncodeScope U)
          (EncodeWord (d := fun _ => 3) s) (c * ((n : ℝ)+1)^e) := by sorry

end NogoodColoring1137.Main
