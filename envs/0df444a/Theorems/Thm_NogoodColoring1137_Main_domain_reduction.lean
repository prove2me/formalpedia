-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_domain_reduction
-- name    : NogoodColoring1137.Main.domain_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:03:35.685975+00:00
-- url     : https://prove2.me/theorems/4b1057ca-ae0d-4faa-aad5-3c793844dac9
-- title:
--   Theorem 3 — Heterogeneous domain reduction and construction time
-- statement:
--   Let $1\le\ell\le n$, $d_v=|D_v|\ge2$, $\sigma=\max_vd_v$, and let $Q$ be any implicit code. A supplied finite program returns a sound nogood on every $\ell$-scope within $T_{\rm ng}$ bit steps. A constructor depending only on that program, with uniform constants, returns $K$ and globally pairwise disjoint boxes satisfying
--   $$Q=\mathop{\dot\bigcup}_{B\in\mathcal B}(Q\cap B),\qquad M_v^B\subsetneq D_v.$$
--   Writing $\Phi_0=\sum_{j<\ell}\binom nj$ and $M=\sum_{j\le\ell}\binom nj$, it retains all bounds
--   $$K=\lfloor\log_{\sigma/(\sigma-1)}\Phi_0\rfloor,\quad |\mathcal B|\le\sum_{j=0}^{\min(K,n)}\binom nj\le(n+1)^K,\quad |\mathcal B|\le\exp(\sigma\ell[\ln(n+1)]^2).$$
--   Also $M\le(n+1)^\ell$, $\ln(\sigma/(\sigma-1))\ge1/\sigma$, and $K\le\sigma\ell\ln(n+1)$. The output $K$ satisfies the exact integer inequalities $\sigma^K\le\Phi_0(\sigma-1)^K$ and $\sigma^{K+1}>\Phi_0(\sigma-1)^{K+1}$. Actual construction time is at most
--   $$\binom n\ell T_{\rm ng}+c(N+1)^e(n+1)^K\sigma nM\ell.$$
--   If $T_{\rm ng}\le a(N+1)^b$, this resource expression is at most $(a+c)(N+1)^{b+e+h}\exp(C\sigma\ell[\ln(n+1)]^2)$ for global $c,C,e,h$. This includes the source construction-time conclusion for every $\sigma$.
--
--   This is the general domain-reduction ingredient. **Formalization Note** $N$ is encoded domains/data length plus the scope bits. $Q$ is never an execution oracle. The exact factors come from §4.3 p.13; no numerical implementation constant is fixed.
--
--   Differences from the source:
--   - encoding: finite coordinates and heterogeneous finite domains → Fin n and Fin (d v), with dependent words on scopes; reason: independent bijective relabeling preserves all words, certificates, boxes and counts
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
--   - generalization: a polynomial-time nogood oracle → any sound finite program with a per-call bound, plus the polynomial-oracle corollary; reason: §4.3 charges oracle work explicitly; every polynomial-time source oracle is included
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Theorem 3, p.10; proof pp.10–13

import Definitions.Def_NogoodColoring1137_Main_DomainEncoding

namespace NogoodColoring1137.Main

/-- Theorem 3, pp.10–13: full domains, exact binomial bound, and actual oracle-charged construction. -/
theorem domain_reduction :
    ∀ oracle : IntMul.MultitapeTM,
      ∃ (P : IntMul.MultitapeTM) (c C : ℝ) (e overhead : ℕ), 0 < c ∧ 0 < C ∧
      ∀ n (d : Fin n → ℕ) (ell : ℕ) (Q : Code d Finset.univ) (data : List Bool)
        (Tng : ℝ),
        (∀ v, 2 ≤ d v) → 1 ≤ ell → ell ≤ n → 0 ≤ Tng →
        NogoodAccess ell Q data oracle Tng →
        let sigma := Sigma d
        let K := LogK n ell sigma
        let N := (EncodeDomains d ell data).length + n
        ∃ (B : List (Box d)) (k : ℕ),
          k = K ∧ sigma^k ≤ PhiZero n ell * (sigma-1)^k ∧
          PhiZero n ell * (sigma-1)^(k+1) < sigma^(k+1) ∧
          Runs P (EncodeDomains d ell data) (EncodeNat k ++ EncodeBoxes B)
            (ConstructionTime n ell sigma K N Tng c e) ∧
          B.Pairwise BoxDisjoint ∧
          (∀ x : Word d Finset.univ,
            x ∈ Q ↔ x ∈ Q ∧ ∃ b ∈ B, InBox b (fun v => x ⟨v, Finset.mem_univ v⟩)) ∧
          (∀ b ∈ B, ∀ v, b v ⊂ Finset.univ) ∧
          B.length ≤ FamilyBound n K ∧ FamilyBound n K ≤ (n+1)^K ∧
          ScopeCount n ell ≤ (n+1)^ell ∧
          (1 / (sigma : ℝ)) ≤ Real.log ((sigma : ℝ) / (sigma-1 : ℕ)) ∧
          (K : ℝ) ≤ sigma * ell * Real.log ((n : ℝ)+1) ∧
          (B.length : ℝ) ≤ Real.exp (sigma * ell * Real.log ((n : ℝ)+1)^2) ∧
          (∀ (a : ℝ) (b : ℕ), 0 < a → Tng ≤ a * ((N : ℝ)+1)^b →
            ConstructionTime n ell sigma K N Tng c e ≤
              (a+c) * ((N : ℝ)+1)^(b+e+overhead) *
                Real.exp (C * sigma * ell * Real.log ((n : ℝ)+1)^2)) := by sorry

end NogoodColoring1137.Main
