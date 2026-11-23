-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_padded_uniformPolyTime
-- name    : NOFSeparation750.CodedGIP.padded_uniformPolyTime
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-22T21:27:30.205885+00:00
-- url     : https://prove2.me/theorems/d7b7aa21-9997-4374-838a-a05daa74a998
-- title:
--   Uniform polynomial-time evaluation of the padded coded-GIP family
-- statement:
--   Let $k\ge2$ and let $a\ge1$ be allowed, i.e. $q=4^a$ satisfies $(32k)^2\le q\le(64k)^2$. Let $\mathbb F$ be a finite field with a fixed bijection $\{0,1\}^{2a}\to\mathbb F$, and let $(V_j,W_j)_{j\ge0}$, $V_j,W_j\le\mathbb F^{r_j}$ with $r_j=(q-\sqrt q)\,q^{j/2}$, be a family of code pairs with ordered bases that is **effective**. This means there are one generator program and one encoding program (finite-control, finite-alphabet multi-stack machines) and one polynomial $p$ such that, for every level $j$, the generator, given $j$ in unary, outputs both generator matrices within $p(r_j)$ steps, and the encoder, given $j$ and a message, outputs the encoded codeword within $p(r_j)$ steps.
--
--   Let $F=(F_n)_{n\ge0}$ be the padded coded-GIP family built from this code family with $\ell=2^{k+2}k$ copies. At length $n$, put $U_j=(\ell+1)\,r_j\,2a$. Let $j$ be the largest level with $U_j\le n$, and evaluate the native coded-GIP function of level $j$ on the prefixes of the $k$ blocks, i.e. test
--   $$\sum_{h=1}^{\ell}a^{(1)}_h\odot\cdots\odot a^{(k)}_h=\sum_{i=1}^k c^{(i)}.$$
--   Below $U_0$ the function is constantly $0$.
--
--   **Claim.** The family $F$ is uniformly polynomial-time computable. There is one finite multi-stack program and one polynomial $P$ such that, for every $n$ and every input $x\in(\{0,1\}^n)^k$, the program, on input $1^n0$ followed by the concatenated blocks, halts with output exactly $F_n(x)$ within $P(kn+n+1)$ steps.
--
--   This isolates the "highly explicit, computable in polynomial time" assertion of Theorem 1.1 (p.3) from the code construction (Theorem 3.2 with Appendix A) and the communication bounds. An evaluator computes the padding level, runs the generator at that level, decodes each forehead into codewords by basis combinations over $\mathbb F$, and compares the two sides of the identity coordinatewise. All of this is polynomial in $r_j\le n$.
--
--   **Formalization Note.** Machines are Mathlib's `Turing.TM2ComputableAux Bool Bool` with all stack alphabets finite (`FiniteProgram`), and running times use `Turing.TM2OutputsInTime`. The statement uses the platform definitions `EffectivePairFamily`, `paddedFamily` and `UniformPolyTime`. No compatibility hypothesis is needed.
-- source:
--   Wang–Wang–Wu, An Explicit and Optimal Separation of BPP from NP in NOF Communication Complexity, STOC 2027 submission #750, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/750.pdf, p.3 (Theorem 1.1 and the following sentence: 'The functions F_n are highly explicit, computable in polynomial time'), p.7 (Theorem 3.2 poly-time construction/encoding; standard padding), Appendix A pp.11–13

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes

namespace NOFSeparation750.CodedGIP
theorem padded_uniformPolyTime (k a : ℕ) (hk : 2 ≤ k) (ha : Allowed k a)
    (F : Type) [Field F] [Fintype F] (D : PairFamily F a)
    (codec : (Fin (2 * a) → Bool) ≃ F) (heff : EffectivePairFamily D codec) :
    UniformPolyTime (paddedFamily D codec k) := by sorry
end NOFSeparation750.CodedGIP
