-- Prove2me | Theorems.Thm_NKtLB_lemma_31
-- name    : NKtLB.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:06:52.326429+00:00
-- url     : https://prove2.me/theorems/676dbd6b-b2a0-4170-b7bc-02ea9a9da7f8
-- title:
--   Lemma 31 — reconstructive pseudorandom generator (corrected: running time $\mathrm{poly}((n+m)/\varepsilon)$)
-- statement:
--   There exist a constant $c$ and a uniform family of triples $(G,A,R^{(-)})$ such that, for all $n,m$ with $1\le m\le2^n$ and every $\varepsilon=1/k$:
--   $$
--   G,A:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m,\qquad R^{(-)}:\{0,1\}^m\times\{0,1\}^d\times\{0,1\}^r\to\{0,1\}^n,
--   $$
--   with $d=O(\log^3(n/\varepsilon))$ and $r=O(m)$. For every $x\in\{0,1\}^n$ and every $D:\{0,1\}^m\to\{0,1\}$ with
--   $$
--   \Pr_{z\sim U_d}[D(G(x;z))=1]-\Pr_{w\sim U_m}[D(w)=1]\ \ge\ \varepsilon,
--   $$
--   the reconstruction succeeds:
--   $$
--   \Pr_{w\sim U_r,\,z\sim U_d}\bigl[R^D(A(x,z),z,w)=x\bigr]\ \ge\ \frac{1}{\mathrm{poly}(m/\varepsilon)} .
--   $$
--   Moreover, $G$, $A$ and $R^D$ (with non-adaptive oracle access to $D$) are computable in time $\mathrm{poly}((n+m)/\varepsilon)$.
--
--   This is the reconstructive generator behind every reconstruction step of §12: a distinguisher for $G(x;\cdot)$ yields a description of $x$ of about $m$ bits.
--
--   Differences from the source:
--   - generalization: "for all sufficiently large $n,m\in\mathbb N$ such that $m\le2^n$" → every $n\ge1$, $1\le m\le 2^n$; reason: Lemma 103 and Algorithm 1 apply the lemma at every output length; small $n$ and $m$ are true by guessing $x$ at random (success $2^{-n}$) and because no distinguisher exists when $m\le d$
--   - generalization: "there exists a triple" for each $n,m,\varepsilon$ → one uniform family (machines for $G$, $A$, $R$ working for all $n,m,k$); reason: Algorithm 1 instantiates $G$ inside an algorithm (p.75), which needs uniformity; a uniform family gives a triple for every $n,m,\varepsilon$
--   - correction: $G$, $A$, $R^D$ computable in time $\mathrm{poly}(n/\varepsilon)$ → time $c((n+m)k)^c+c$; reason: the printed bound is false for $m>\mathrm{poly}(n/\varepsilon)$: e.g. $m=2^n$, $\varepsilon=1/2$, where writing the $m$ output bits of $G$ takes $m$ steps; every application has $m=O(n)$, where the bounds agree
--   - encoding: real $\varepsilon>0$ → $\varepsilon=1/k$, $k\in\mathbb N_{\ge1}$; reason: the case of a real $\varepsilon\in(0,1]$ is $k=\lceil1/\varepsilon\rceil$, with constants changed by a factor; $\varepsilon>1$ admits no distinguisher
--   - encoding: $O(f)$, $\mathrm{poly}(f)$ → $C f+C$, $\lceil C f^C\rceil+C$ with $C$ quantified before the data; reason: standard meaning; constants are chosen in the order the statement reads
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 31, pp.26–27

import Mathlib
import Definitions.Def_NKtLB_IsReconstructivePRG

namespace NKtLB

/-- **Lemma 31 (the reconstructive PRG)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 31, pp.26–27): "For all sufficiently large
`n, m ∈ ℕ` such that `m ≤ 2^n` and any `ε > 0`, there exists a triple `(G, A, R^{(-)})` such that
`G : {0,1}^n × {0,1}^d → {0,1}^m`, `A : {0,1}^n × {0,1}^d → {0,1}^m`,
`R^{(-)} : {0,1}^m × {0,1}^d × {0,1}^r → {0,1}^n`, and for every `x ∈ {0,1}^n` and any
`D : {0,1}^m → {0,1}` such that `Pr_{z∼U_d}[D(G(x; z)) = 1] − Pr_{w∼U_m}[D(w) = 1] ≥ ε`, it holds
that `Pr_{w∼U_r, z∼U_d}[R^D(A(x, z), z, w) = x] ≥ 1/poly(m/ε)`. Here, we have `d = O(log³(n/ε))` and
`r = O(m)`. Moreover, `G` and `A` can be computed in time `poly(n/ε)`, and `R^D` can be computed in
time `poly(n/ε)` with non-adaptive oracle access to `D`."

There are a constant `c` and a uniform family `F` with `IsReconstructivePRG c F`.

**Formalization Note.** See `IsReconstructivePRG`: `ε = 1/k`; one machine for all `n, m, k`;
reconstruction for every `n ≥ 1`, `1 ≤ m ≤ 2^n`; running time `poly((n+m)/ε)` (the printed
`poly(n/ε)` is impossible for `m > poly(n/ε)`, as the output has `m` bits). -/
theorem lemma_31 : ∃ (c : ℕ) (F : PRGFamily), IsReconstructivePRG c F := by sorry

end NKtLB
