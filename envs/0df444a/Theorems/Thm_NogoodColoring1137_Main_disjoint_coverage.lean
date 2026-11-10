-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_disjoint_coverage
-- name    : NogoodColoring1137.Main.disjoint_coverage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:10.368436+00:00
-- url     : https://prove2.me/theorems/f82cdf70-0432-4de7-b3a3-a7549f78a56e
-- title:
--   Lemma 4.3 — Algorithm 1 disjoint coverage
-- statement:
--   Let $1\le\ell\le n$, every domain have at least two labels, and every supplied $\ell$-scope certificate be sound for $Q$. Initialize exactly those entries and use $K=\lfloor\log_{\sigma/(\sigma-1)}\Phi_0\rfloor$. The actual Algorithm 1 boxes satisfy
--   $$A\ne A'\implies B_A\cap B_{A'}=\varnothing,\qquad Q\subseteq\bigcup_{|A|\le\min(K,n)}B_A.$$
--   Disjointness holds in the full product, including words outside the code. Replays share the same initial table and first-minimum tie breaking. This is the partition input for Theorem 3.
--
--   **Formalization Note** The certificate function is total on scopes for typing convenience; its values away from exact-$\ell$ scopes are unused.
--
--   Differences from the source:
--   - encoding: finite coordinates and heterogeneous finite domains → Fin n and Fin (d v), with dependent words on scopes; reason: independent bijective relabeling preserves all words, certificates, boxes and counts
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 4.3, pp.12–13

import Definitions.Def_NogoodColoring1137_Main_Replay

namespace NogoodColoring1137.Main

/-- Lemma 4.3, pp.12–13: the boxes of Algorithm 1, not arbitrary witnesses. -/
theorem disjoint_coverage {n : ℕ} (d : Fin n → ℕ) (hd : ∀ v, 2 ≤ d v)
    (ell : ℕ) (hell : 1 ≤ ell ∧ ell ≤ n) (Q : Code d Finset.univ)
    (cert : (T : Finset (Fin n)) → Word d T)
    (hcert : ∀ T, T.card = ell → Nogood Q T (cert T)) :
    let W := InitialTable ell cert
    let E := ExceptionSets n (LogK n ell (Sigma d))
    (∀ A ∈ E, ∀ B ∈ E, A ≠ B →
      BoxDisjoint (Replay (fun v => lt_of_lt_of_le (by decide : 0 < 2) (hd v)) ell W A)
        (Replay (fun v => lt_of_lt_of_le (by decide : 0 < 2) (hd v)) ell W B)) ∧
    ∀ x ∈ Q, ∃ A ∈ E,
      InBox (Replay (fun v => lt_of_lt_of_le (by decide : 0 < 2) (hd v)) ell W A)
        (fun v => x ⟨v, Finset.mem_univ v⟩) := by sorry

end NogoodColoring1137.Main
