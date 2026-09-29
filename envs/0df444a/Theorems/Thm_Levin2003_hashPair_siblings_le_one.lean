-- Prove2me | Theorems.Thm_Levin2003_hashPair_siblings_le_one
-- name    : Levin2003.hashPair_siblings_le_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T22:02:48.692466+00:00
-- url     : https://prove2.me/theorems/9d8343be-12f5-4565-b208-6a967bea002e
-- title:
--   Remark: $g(a,x) = (a, f(x) + ax)$ has at most one sibling per input on average
-- statement:
--   **Remark (Levin 2003, Section 4.3, p. 102).** *Inputs of $g(a,x) = (a, f(x) + ax)$ have $\le 1$ siblings on average for any length-preserving $f$ and $a, x \in \mathrm{GF}_{2^{\Vert x \Vert}}$.*
--
--   Here a *sibling* of an input is a different input with the same image, and the average is over all inputs. Formally, for $n \ge 1$ and any function $f$ on the field $\mathbb{F}_{2^{n}}$, the number of ordered pairs of distinct inputs with the same image under $g$ is at most the number of inputs, $2^{2n}$.
--
--   The point of the Remark is that raw one-way functions are hard to use: 'To be useful, owfs need other properties, e.g. low Renyi entropy', and the hashing $g$ is proposed as a way to obtain it, the low average collision count being exactly the required entropy bound. The paper's accompanying Conjecture — that $g$ is one-way for any one-way $f$, with the same security up to a polynomial factor — is not part of this statement.
--
--   The count is in fact exact: for distinct $x, x'$, the equation $f(x) + ax = f(x') + ax'$ determines $a$ uniquely as $(f(x) + f(x'))/(x + x')$, so there are $2^{n}(2^{n}-1)$ ordered sibling pairs, slightly fewer than the $2^{2n}$ inputs.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3, p. 102, Remark

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- **Remark (Levin 2003, §4.3).** For every function `f` on the field with
`2 ^ n` elements, the map `g (a, x) = (a, f x + a * x)` has at most one sibling
per input on average: the number of ordered pairs of distinct inputs with the
same image is at most the number of inputs. -/
theorem hashPair_siblings_le_one (n : ℕ) (hn : n ≠ 0)
    (f : GaloisField 2 n → GaloisField 2 n) :
    {pq : (GaloisField 2 n × GaloisField 2 n) × (GaloisField 2 n × GaloisField 2 n) |
        pq.1 ≠ pq.2 ∧ hashPair f pq.1 = hashPair f pq.2}.ncard
      ≤ Nat.card (GaloisField 2 n × GaloisField 2 n) := by
  sorry

end Levin2003
