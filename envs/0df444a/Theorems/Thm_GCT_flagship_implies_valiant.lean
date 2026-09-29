-- Prove2me | Theorems.Thm_GCT_flagship_implies_valiant
-- name    : GCT.flagship_implies_valiant
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:34:29.975779+00:00
-- url     : https://prove2.me/theorems/a68a61af-9f2b-4771-aba4-6ab56ec33ac4
-- title:
--   The flagship conjecture implies Valiant's conjecture
-- statement:
--   The GCT flagship conjecture implies Valiant's conjecture: if the border determinantal complexity $\overline{\mathrm{dc}}(\mathrm{perm}_m)$ grows faster than any polynomial in $m$, then so does $\mathrm{dc}(\mathrm{perm}_m)$. This is immediate from $\overline{\mathrm{dc}}(\mathrm{perm}_m) \le \mathrm{dc}(\mathrm{perm}_m)$, and records formally why the Zariski-closed version of the conjecture is a strengthening of Valiant's.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, p. 16, §1.2.5 ('The "Zariski closed" version of Conjecture 1.2.4.2 is the flagship conjecture of Geometric Complexity Theory'); cf. J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, p. 4, §2.1.

import Definitions.Def_GCT_determinantal_complexity

namespace GCT

theorem flagship_implies_valiant
    (h : ∀ c : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → m ^ c < dcBar m) :
    ∀ c : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → m ^ c < dc m := by sorry

end GCT
