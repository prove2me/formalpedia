-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_theorem_2
-- name    : GOSNIZK.BGNCommit.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:34.710983+00:00
-- url     : https://prove2.me/theorems/c7174ce7-6dd2-4f3b-894d-98f3cad14275
-- title:
--   Theorem 2 (exact part) — the BGN scheme of Figure 1 has all the perfect properties of a homomorphic proof commitment
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$: primes $p < q$, groups $\mathbb G, \mathbb G_T$ of order $n$, a bilinear map $e$, a generator $g$ of $\mathbb G$ with $e(g,g)$ generating $\mathbb G_T$. Consider the commitment scheme of Figure 1: $\mathrm{com}(m; r) = g^m h^r$, binding keys $h = g^{px}$ ($x \in \mathbb Z_q^*$), hiding keys $h = g^x$ with trapdoor $x \in \mathbb Z_n^*$, $\mathrm{Topen}_x(m, r, m') = r - (m'-m)/x$, $P_{01}(m, r) = (g^{2m-1}h^r)^r$, $V_{01}(c, \pi)$: $e(c, cg^{-1}) = e(h, \pi)$, and $\mathrm{Ext}$ the exhaustive search for $m$ with $c^q = (g^q)^m$. Then:
--
--   1. **Homomorphic property.** On either kind of key, $\mathrm{com}(m_1 + m_2; r_1 + r_2) = \mathrm{com}(m_1; r_1)\,\mathrm{com}(m_2; r_2)$.
--   2. **Perfect binding.** On a binding key, $\mathrm{com}(m_1; r_1) = \mathrm{com}(m_2; r_2)$ implies $m_1 \equiv m_2 \pmod p$.
--   3. **Perfect trapdoor opening.** On a hiding key, $\mathrm{com}(m_2; \mathrm{Topen}_x(m_1, r_1, m_2)) = \mathrm{com}(m_1; r_1)$.
--   4. **Perfect trapdoor opening indistinguishability.** On a hiding key, for all $m_1, m_2$, if $r_1$ is uniform on $\mathbb Z_n$ then $\mathrm{Topen}_x(m_1, r_1, m_2)$ is uniform on $\mathbb Z_n$.
--   5. **Perfect completeness.** On either kind of key, for $m \in \{0,1\}$ and every $r$, $V_{01}$ accepts $(\mathrm{com}(m; r), P_{01}(m, r))$.
--   6. **Perfect soundness.** On a binding key, if $V_{01}$ accepts $(c, \pi)$ then $c = \mathrm{com}(m; r)$ for some $m \in \{0,1\}$ and $r \in \mathbb Z_n$.
--   7. **Perfect witness indistinguishability.** On a hiding key, $\mathrm{com}(0; r_0) = \mathrm{com}(1; r_1)$ implies $P_{01}(0, r_0) = P_{01}(1, r_1)$.
--   8. **Perfect non-erasure witness indistinguishability.** On a hiding key, for $m \in \{0,1\}$, $\mathrm{com}(m; r_0) = \mathrm{com}(1-m; r_1)$ implies $P_{01}(m, r_0) = P_{01}(1-m, r_1)$.
--   9. **Perfect extractability.** On a binding key, for $m \in \{0,1\}$ and every $r$, $\mathrm{Ext}(\mathrm{com}(m; r)) = m$.
--
--   In the paper these properties, together with the computational indistinguishability of the two kinds of keys, make Figure 1 a homomorphic proof commitment with perfect extraction and perfect non-erasure witness indistinguishability; this scheme instantiates the paper's perfectly sound NIZK proofs and perfect NIZK arguments for Circuit SAT.
--
--   **Formalization Note**
--   - Only the exact part of Theorem 2 is formalized. Key indistinguishability, the clause "if the subgroup decision assumption holds for $\mathcal G_{\mathrm{BGN}}$" and Definition 1 are computational and are dropped.
--   - Each "for all adversaries, probability $1$" property is stated for every key in the support of the corresponding key generator and every input an adversary could choose, which is equivalent for unbounded adversaries.
--   - Witness indistinguishability (7) is stated as equality of the proofs: the prover is deterministic, so equal proofs are equal distributions. For (8) the proof randomness space is trivial and the simulator $S_{01}$ returns the empty randomness, so the paper's distributional definition reduces to this equality.
--   - Trapdoor opening indistinguishability (4) is the equality of the distributions (`PMF`s) of $\mathrm{Topen}_x(m_1, r_1, m_2)$ for uniform $r_1$ and of a uniform $r_2$, for each pair $(m_1, m_2)$; this gives the paper's equality for every adversary, including randomized ones.
--   - Messages are elements of $\mathbb Z_n$ and are compared modulo $p$ in (2) and (9); $\mathrm{Ext}$ returns an element of $\mathbb Z_p$. The paper's requirement that the message space have order at least $3$ is not part of the statement: it holds exactly when $p \ge 3$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, Theorem 2 (with the properties of Section 3, pp. 7–8, and Figure 1, p. 10)

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem theorem_2 {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) :
    -- (1) homomorphic property, on either kind of key
    (∀ h : G, (S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x) →
      ∀ m₁ r₁ m₂ r₂ : ZMod S.n, S.com h (m₁ + m₂) (r₁ + r₂) = S.com h m₁ r₁ * S.com h m₂ r₂) ∧
    -- (2) perfect binding (messages live in ℤ_p)
    (∀ h : G, S.IsBindingKey h →
      ∀ m₁ r₁ m₂ r₂ : ZMod S.n, S.com h m₁ r₁ = S.com h m₂ r₂ → S.toZp m₁ = S.toZp m₂) ∧
    -- (3) perfect trapdoor opening
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ m₁ r₁ m₂ : ZMod S.n, S.com h m₂ (S.Topen x m₁ r₁ m₂) = S.com h m₁ r₁) ∧
    -- (4) perfect trapdoor opening indistinguishability: Topen(m₁, r₁, m₂) with r₁ uniform is uniform
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ m₁ m₂ : ZMod S.n,
        (PMF.uniformOfFintype (ZMod S.n)).map (fun r₁ => S.Topen x m₁ r₁ m₂) =
          PMF.uniformOfFintype (ZMod S.n)) ∧
    -- (5) perfect completeness, on either kind of key
    (∀ h : G, (S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x) →
      ∀ m r : ZMod S.n, (m = 0 ∨ m = 1) → S.V01 h (S.com h m r) (S.P01 h m r)) ∧
    -- (6) perfect soundness on binding keys
    (∀ h : G, S.IsBindingKey h →
      ∀ c π : G, S.V01 h c π → ∃ m r : ZMod S.n, (m = 0 ∨ m = 1) ∧ c = S.com h m r) ∧
    -- (7) perfect witness indistinguishability on hiding keys
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ r₀ r₁ : ZMod S.n, S.com h 0 r₀ = S.com h 1 r₁ → S.P01 h 0 r₀ = S.P01 h 1 r₁) ∧
    -- (8) perfect non-erasure witness indistinguishability (empty proof randomness, S01 trivial)
    (∀ (h : G) (x : ZMod S.n), S.IsHidingKey h x →
      ∀ m r₀ r₁ : ZMod S.n, (m = 0 ∨ m = 1) → S.com h m r₀ = S.com h (1 - m) r₁ →
        S.P01 h m r₀ = S.P01 h (1 - m) r₁) ∧
    -- (9) perfect extractability on binding keys
    (∀ h : G, S.IsBindingKey h →
      ∀ m r : ZMod S.n, (m = 0 ∨ m = 1) → S.Ext (S.com h m r) = S.toZp m) := by sorry

end GOSNIZK.BGNCommit
