-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_A_1
-- name    : NetUnrelEst.Main.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:19.086848+00:00
-- url     : https://prove2.me/theorems/da809886-c1c2-4619-8f6a-754a99efb61e
-- title:
--   Lemma A.1 — the random multiplicity π^N is unbiased for p with second moment at most p^{2−η}
-- statement:
--   Fix $0<\eta<1$ and $\pi=1-\eta$. For a failure probability $0<p\le1$, choose an integer $k\ge0$ with $\pi^{k+1}\le p\le\pi^k$ and write $p=\pi^k y$, so $\pi\le y\le1$. Let $N=k+1$ with probability $\rho=(1-y)/(1-\pi)$ and $N=k$ otherwise, and put $Z=\pi^N$. Then $\rho\in[0,1]$ and
--   $$\mathbb EZ=p,\qquad \mathbb EZ^2\le p^{2-\eta}.\tag{59}$$
--
--   This is the random parallel-edge representation of §2.6: an edge of failure probability $p$ becomes $N$ parallel edges each failing with probability $\pi$. The representation keeps the failure law and adds only a small amount of second moment, which the variance analysis of §3 uses through (26).
--
--   **Formalization Note.** The two-point law is written out: $\mathbb EZ=(1-\rho)\pi^k+\rho\pi^{k+1}$ and $\mathbb EZ^2=(1-\rho)\pi^{2k}+\rho\pi^{2k+2}$; $p^{2-\eta}$ is a real power.
--
--   Differences from the source:
--   - generalization: the paper's η = 1/(256H), H = log(8n), and an edge of failure probability 0 < p < 1 → every 0 < η < 1 and every 0 < p ≤ 1; reason: the proof uses only 0 < η < 1 and 0 < p ≤ 1; the paper's η and p are instances
--   - encoding: the adjacent-integer choice k, k+1 with π^{k+1} ≤ p ≤ π^k → any natural k with π^{k+1} ≤ p ≤ π^k; the law of N written as weights 1 − ρ, ρ, with the clause 0 ≤ ρ ≤ 1; reason: at p = π^k both adjacent choices give N = k almost surely, so the law is the same; the clause only says the two-point law is a probability law
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 32, Lemma A.1

import Mathlib
import Definitions.Def_NetUnrelEst_Main_Contraction

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma A.1.** For `0 < η < 1`, `π = 1 − η` and `0 < p ≤ 1`, let `k` be an adjacent integer,
`π^{k+1} ≤ p ≤ π^k`, write `p = π^k y`, and let `N = k + 1` with probability `ρ = (1 − y)/(1 − π)`
and `N = k` otherwise. Then `ρ ∈ [0, 1]`, `Z = π^N` has `EZ = p` and `EZ² ≤ p^{2−η}`. Sun 2027,
p. 32, Lemma A.1, (59). -/
theorem lemma_A_1 (η p : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) (k : ℕ)
    (hk1 : piOf η ^ (k + 1) ≤ p) (hk2 : p ≤ piOf η ^ k) :
    (0 ≤ (1 - p / piOf η ^ k) / (1 - piOf η) ∧ (1 - p / piOf η ^ k) / (1 - piOf η) ≤ 1) ∧
    (1 - (1 - p / piOf η ^ k) / (1 - piOf η)) * piOf η ^ k +
        (1 - p / piOf η ^ k) / (1 - piOf η) * piOf η ^ (k + 1) = p ∧
    (1 - (1 - p / piOf η ^ k) / (1 - piOf η)) * (piOf η ^ k) ^ 2 +
        (1 - p / piOf η ^ k) / (1 - piOf η) * (piOf η ^ (k + 1)) ^ 2 ≤ p ^ (2 - η) := by sorry

end NetUnrelEst.Main
