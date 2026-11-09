-- Prove2me | Theorems.Thm_NKtLB_exists_valid_universal
-- name    : NKtLB.exists_valid_universal
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:12:29.16722+00:00
-- url     : https://prove2.me/theorems/6d8ae75c-e933-4c4c-a290-640c3ac88a9c
-- title:
--   §3.2 — time-efficient universal machines exist
-- statement:
--   There exist a machine $U$ and a machine code $\langle\cdot\rangle$ such that:
--
--   1. $U$ is **time-efficient**: for every machine $U'$ there is $C$ with $K^{C t(\lceil\log t\rceil+1)+C}_U(x)\le K^t_{U'}(x)+C$ for all $x$ and $t$; and
--   2. $U$ **simulates every machine**: for each machine $M$ there is $c_M$ such that $U$ on $s_\alpha01\langle M\rangle\alpha$ reproduces every halting run of $M(\alpha;x;w;r)$ of at most $t$ steps within $c_M t(\lceil\log t\rceil+1)+c_M$ steps, with the same output and any oracle, and passes the queries of $M$ through.
--
--   Every statement of the mission assumes such a machine, so this theorem rules out a vacuous hypothesis. The paper cites the existence of time-efficient machines to Li and Vitányi.
--
--   Differences from the source:
--   - reading: $U$ runs in time $\tilde O(|M|,t)$ → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$, with queries passed through; reason: quasi-linear overhead is what Eq. (30) needs; the additive $c_M$ covers $t\le1$
--   - reading: "time-efficient machines exist" (one sentence) → existence of a pair satisfying both §3.2 assumptions (time-efficiency and simulation); reason: the paper fixes one machine with both properties; existence of the pair is what the hypothesis `IsValidUniversal` needs
--   - encoding: $K^{C\cdot t\log t}_U$ → $K^{C t(\lceil\log t\rceil+1)+C}_U$; reason: read literally, the bound is $0$ for $t\le1$ and no machine qualifies; for $t\ge2$ the two agree up to the constant
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21 (unnumbered)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal

namespace NKtLB

/-- **Time-efficient universal machines exist** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21, unnumbered): "We say that a
(universal) machine `U` is time-efficient if for every machine `U′` there is a constant `C` such
that, for every string `x` and time bound `t`, we have `K^{C·t log t}_U(x) ≤ K^t_{U′}(x) + C`. It is
known that time-efficient machines exist (see, e.g., [LV19])."

There are a machine `U` and a machine encoding `code` such that `U` is time-efficient and simulates
every machine through the program format `s_α 01 ⟨M⟩ α` with overhead `c_M · t · (⌈log t⌉ + 1) + c_M`
(`IsValidUniversal`). This guards every statement of the mission against vacuity.

**Formalization Note.** Readings R1, R2 (see `IsTimeEfficient`, `Simulates`). -/
theorem exists_valid_universal :
    ∃ (U : Machine) (code : Machine → List Bool), IsValidUniversal U code := by sorry

end NKtLB
