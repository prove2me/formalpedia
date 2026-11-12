-- Prove2me | Theorems.Thm_OracleSNARG_PublicLB_robustness
-- name    : OracleSNARG.PublicLB.robustness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:48:52.390781+00:00
-- url     : https://prove2.me/theorems/fe0123be-92fe-4c25-b35e-a3fa10154275
-- title:
--   §6, Robustness — $C^{O_{h,r}}$ is $1/4$-robust on every input
-- statement:
--   Fix $\lambda$ and a scheme $S=(\mathrm{Gen},P,V)$ whose verifier makes at most $\ell=\ell(\lambda)$ oracle queries on every input, against every oracle, with $8\ell\le N=N(\lambda)$. Then for every function $h:\{0,1\}^{n}\to\{0,1\}^k$, every prover coin vector $r$ and every bit string $x$, the majority computation with oracle $O_{h,r}$ (Equation (5)) is $1/4$-robust on $x$:
--   $$C^{O_{h,r}}(x)=1\quad\text{or}\quad \forall a\in\{0,1\}^N:\ \mathrm{Maj}(a)=1\ \Rightarrow\ \mathrm{err}_{O_{h,r}}(a)\ \ge\ \tfrac14 N .$$
--   The reason given in the paper is that every row of $O_{h,r}$ is either all ones or has at most $\ell\le N/8$ ones. Changing at most $N/4$ answers therefore cannot change the majority. This is what makes the false statement of the proof a robust one.
--
--   Differences from the source:
--
--   - generalization: h sampled from the pairwise-independent family, every input x ∈ {0,1}^n → every function h, every prover coin vector r and every bit string x of any length; reason: robustness is a property of each single oracle O_{h,r} and rows of other lengths are all ones, so the statement specializes to the paper's
--   - generalization: a SNARG (Gen, P, V) with polynomial-time algorithms (Definition 9) and k = log2(2ℓ) → any scheme (no efficiency or completeness assumed) and any output length k of h; reason: the paragraph uses only the query bound ℓ ≤ N/8 of V, so it specializes to the paper's
--   - encoding: "V makes ℓ ≤ N/8 queries" → the verifier's decision trees at λ have depth ≤ ℓ(λ) on every (crs, x, π), and 8ℓ(λ) ≤ N(λ); reason: depth bounds the queries against every oracle
--   - encoding: row positions i ∈ [N] and queries (x, i) → positions 0, …, N − 1 and the string 1^i 0 x; reason: a fixed injective pair encoding, as the paper leaves it unspecified
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 26, §6, Robustness paragraph

import Mathlib
import Definitions.Def_OracleSNARG_PublicLB_Majority
import Definitions.Def_OracleSNARG_PublicLB_Scheme
import Definitions.Def_OracleSNARG_PublicLB_ProofObjects

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **§6, Robustness paragraph**, p. 26 of Goldwasser, Kalai (manuscript sha256 cc66f0af…): "Note
that the computation C^{O_{h,r}} is 1/4-robust on every input. This is the case since every row of
O_{h,r} is either all ones or contains at most ℓ ≤ N/8 ones." At a fixed `λ`, for a verifier making
at most `ℓ(λ) ≤ N(λ)/8` queries on every input, every hash function `h` and all prover coins `r`. -/
theorem robustness (n N ℓ : ℕ → ℕ) (S : Scheme) (lam : ℕ)
    (hV : ∀ crs x π, (S.verifier lam crs x π).depth ≤ ℓ lam)
    (hℓN : 8 * ℓ lam ≤ N lam) {k : ℕ} (h : Hash (n lam) k)
    (r : Fin (S.prover lam).coins → Bool) (x : List Bool) :
    Robust (1 / 4) (Ohr S n N lam h r) (N lam) x := by sorry

end OracleSNARG.PublicLB
