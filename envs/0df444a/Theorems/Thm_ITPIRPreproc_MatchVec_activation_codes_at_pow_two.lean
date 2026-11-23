-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_activation_codes_at_pow_two
-- name    : ITPIRPreproc.MatchVec.activation_codes_at_pow_two
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:22.09411+00:00
-- url     : https://prove2.me/theorems/cbaf1a03-fe6b-41d4-86b4-deb9e837ae2e
-- title:
--   Claim 6.2.4 — exact fixed-width encodings at real sizes
-- statement:
--   At a real size $m=2^h$, assume $d=\dim(h)>0$. The activation-bit key code, consisting of $h+1$ row-major Boolean vectors of length $d$, is injective and has length $(h+1)d$. The hint and answer codes, consisting of two bits per $\mathbb F_3$ coordinate, are injective and have length $2d$. These are precisely the encoding, length and decoding obligations of the non-streaming part of Claim 6.2.4. The assumption $d>0$ for keys is necessary because all key encodings are empty when $d=0$; no positivity assumption is needed for the hint and answer vectors.
-- source:
--   Claim 6.2.4, printed p.23 (PDF p.25), and Appendix A, pp.35–37: exact encodings and attractable algorithms for the activation-bit primitive (14)–(17). The key rows are encoded in $\mathbb F_2$ and hint/answer coordinates in $\mathbb F_3$, with fixed-width injective codes.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationCodeAlgebra

namespace ITPIRPreproc.MatchVec

open WordRAM

theorem activation_codes_at_pow_two (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (h : ℕ)
    (hd : 0 < dim h) :
    Function.Injective (actEncKey dim u v (2 ^ h)) ∧
      Function.Injective (actEncHint dim u v (2 ^ h)) ∧
      Function.Injective (actEncAns dim u v (2 ^ h)) ∧
      (∀ K, (actEncKey dim u v (2 ^ h) K).length = (h + 1) * dim h) ∧
      (∀ z, (actEncHint dim u v (2 ^ h) z).length = 2 * dim h) ∧
      (∀ z, (actEncAns dim u v (2 ^ h) z).length = 2 * dim h) := by sorry
